//===--- DeadFunctionElimination.cpp - Eliminate dead functions -----------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2017 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "sil-dead-function-elimination"
#include "swift/AST/ProtocolConformance.h"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "swift/SIL/PatternMatch.h"
#include "swift/SIL/SILBuilder.h"
#include "swift/SIL/SILVisitor.h"
#include "swift/SIL/InstructionUtils.h"
#include "swift/SILOptimizer/Utils/Local.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
using namespace swift;

STATISTIC(NumDeadFunc, "Number of dead functions eliminated");
STATISTIC(NumEliminatedExternalDefs, "Number of external function definitions eliminated");

namespace {

/// Returns true if a function should be SIL serialized or emitted by IRGen.
static bool shouldBeSerializedOrEmitted(SILFunction *F) {
  if (F->isAvailableExternally() && hasPublicVisibility(F->getLinkage()) &&
      !F->isTransparent())
    return false;
  return true;
}

/// This is a base class for passes that are based on function liveness
/// computations like e.g. dead function elimination.
/// It provides a common logic for computing live (i.e. reachable) functions.
class FunctionLivenessComputation {
protected:

  /// Represents a function which is implementing a vtable or witness table
  /// method.
  struct FuncImpl {
    FuncImpl(SILFunction *F, ClassDecl *Cl) : F(F) { Impl.Cl = Cl; }
    FuncImpl(SILFunction *F, ProtocolConformance *C) : F(F) { Impl.Conf = C; }

    /// The implementing function.
    SILFunction *F;

    union {
      /// In case of a vtable method.
      ClassDecl *Cl;

      /// In case of a witness method.
      ProtocolConformance *Conf;
    } Impl;
  };

  /// Stores which functions implement a vtable or witness table method.
  struct MethodInfo {

    MethodInfo(bool isWitnessMethod) :
      methodIsCalled(false), isWitnessMethod(isWitnessMethod) {}

    /// All functions which implement the method. Together with the class for
    /// which the function implements the method. In case of a witness method,
    /// the class pointer is null.
    SmallVector<FuncImpl, 8> implementingFunctions;

    /// True, if the method is called, meaning that any of it's implementations
    /// may be called.
    bool methodIsCalled;

    /// True if this is a witness method, false if it's a vtable method.
    bool isWitnessMethod;

    /// Adds an implementation of the method in a specific class.
    void addClassMethodImpl(SILFunction *F, ClassDecl *C) {
      assert(!isWitnessMethod);
      implementingFunctions.push_back(FuncImpl(F, C));
    }

    /// Adds an implementation of the method in a specific conformance.
    void addWitnessFunction(SILFunction *F, ProtocolConformance *Conf) {
      assert(isWitnessMethod);
      implementingFunctions.push_back(FuncImpl(F, Conf));
    }
  };

  SILModule *Module;

  llvm::DenseMap<AbstractFunctionDecl *, MethodInfo *> MethodInfos;
  llvm::SpecificBumpPtrAllocator<MethodInfo> MethodInfoAllocator;

  llvm::SmallSetVector<SILFunction *, 16> Worklist;

  llvm::SmallPtrSet<void *, 32> AliveFunctionsAndTables;

  bool skipIndirectMethodInvocations = false;

  void setSkipIndirectMethodInvocations() {
    skipIndirectMethodInvocations = true;
  }

  bool shouldSkipIndirectMethodInvocations() const {
    return skipIndirectMethodInvocations;
  }

  /// Checks is a function is alive, e.g. because it is visible externally.
  bool isAnchorFunction(SILFunction *F) {

    // Remove internal functions that are not referenced by anything.
    if (isPossiblyUsedExternally(F->getLinkage(), Module->isWholeModule()))
      return true;

    // Do not consider public_external functions that do not need to be emitted
    // into the client as anchors.
    if (!shouldBeSerializedOrEmitted(F))
      return false;

    // ObjC functions are called through the runtime and are therefore alive
    // even if not referenced inside SIL.
    if (F->getRepresentation() == SILFunctionTypeRepresentation::ObjCMethod)
      return true;

    // If function is marked as "keep-as-anchor", don't remove it.
    if (F->isKeepAsAnchor())
      return true;

    // If function is marked as "keep-as-public", don't remove it.
    // Change its linkage to public, so that other applications can refer to it.
    // It is important that this transformation is done at the end of
    // a pipeline, as it may break some optimizations.
    if (F->isKeepAsPublic()) {
      F->setLinkage(SILLinkage::Public);
      DEBUG(llvm::dbgs() << "DFE: Preserve the specialization "
                         << F->getName() << '\n');
      return true;
    }

    return false;
  }

  /// Gets or creates the MethodInfo for a vtable or witness table method.
  /// \p decl The method declaration. In case of a vtable method this is always
  ///         the most overridden method.
  MethodInfo *getMethodInfo(AbstractFunctionDecl *decl, bool isWitnessMethod) {
    MethodInfo *&entry = MethodInfos[decl];
    if (entry == nullptr) {
      entry = new (MethodInfoAllocator.Allocate()) MethodInfo(isWitnessMethod);
    }
    assert(entry->isWitnessMethod == isWitnessMethod);
    return entry;
  }

  /// Returns true if a function is marked as alive.
  bool isAlive(SILFunction *F) {
    return AliveFunctionsAndTables.count(F) != 0;
  }

  /// Returns true if a witness table is marked as alive.
  bool isAlive(SILWitnessTable *WT) {
    return AliveFunctionsAndTables.count(WT) != 0;
  }

  /// Marks a function as alive.
  void makeAlive(SILFunction *F) {
    // Do not mark functions that do not need to be serialized as alive.
    // We don't need to scan their bodies.
    //if (!shouldBeSerializedOrEmitted(F))
    //  return;
    DEBUG(llvm::dbgs() << "    makeAlive " << F->getName() << '\n');
    AliveFunctionsAndTables.insert(F);
    assert(F && "function does not exist");
    Worklist.insert(F);
  }

  /// Marks all contained functions and witness tables of a witness table as
  /// alive.
  void makeAlive(SILWitnessTable *WT) {
    DEBUG(llvm::dbgs() << "    scan witness table " << WT->getName() << '\n');

    AliveFunctionsAndTables.insert(WT);
    for (const SILWitnessTable::Entry &entry : WT->getEntries()) {
      switch (entry.getKind()) {
        case SILWitnessTable::Method: {

          auto methodWitness = entry.getMethodWitness();
          auto *fd = cast<AbstractFunctionDecl>(methodWitness.Requirement.
                                                getDecl());
          assert(fd == getBase(fd) && "key in witness table is overridden");
          SILFunction *F = methodWitness.Witness;
          if (F) {
            MethodInfo *MI = getMethodInfo(fd, /*isWitnessMethod*/ true);
            if (MI->methodIsCalled || !F->isDefinition())
              ensureAlive(F);
          }
        } break;

        case SILWitnessTable::AssociatedTypeProtocol: {
          ProtocolConformanceRef CRef =
             entry.getAssociatedTypeProtocolWitness().Witness;
          if (CRef.isConcrete())
            ensureAliveConformance(CRef.getConcrete());
          break;
        }
        case SILWitnessTable::BaseProtocol:
          ensureAliveConformance(entry.getBaseProtocolWitness().Witness);
          break;

        case SILWitnessTable::Invalid:
        case SILWitnessTable::MissingOptional:
        case SILWitnessTable::AssociatedType:
          break;
      }
    }

  }
  
  /// Marks the declarations referenced by a key path pattern as alive if they
  /// aren't yet.
  void ensureKeyPathComponentsAreAlive(KeyPathPattern *KP) {
    for (auto &component : KP->getComponents()) {
      switch (component.getKind()) {
      case KeyPathPatternComponent::Kind::SettableProperty:
        ensureAlive(component.getComputedPropertySetter());
        LLVM_FALLTHROUGH;
      case KeyPathPatternComponent::Kind::GettableProperty: {
        ensureAlive(component.getComputedPropertyGetter());
        auto id = component.getComputedPropertyId();
        switch (id.getKind()) {
        case KeyPathPatternComponent::ComputedPropertyId::DeclRef: {
          auto decl = cast<AbstractFunctionDecl>(id.getDeclRef().getDecl());
          if (auto clas = dyn_cast<ClassDecl>(decl->getDeclContext())) {
            ensureAliveClassMethod(getMethodInfo(decl, /*witness*/ false),
                                   dyn_cast<FuncDecl>(decl),
                                   clas);
          } else if (isa<ProtocolDecl>(decl->getDeclContext())) {
            ensureAliveProtocolMethod(getMethodInfo(decl, /*witness*/ true));
          } else {
            llvm_unreachable("key path keyed by a non-class, non-protocol method");
          }
          break;
        }
        case KeyPathPatternComponent::ComputedPropertyId::Function:
          ensureAlive(id.getFunction());
          break;
        case KeyPathPatternComponent::ComputedPropertyId::Property:
          break;
        }
        
        if (auto equals = component.getComputedPropertyIndexEquals())
          ensureAlive(equals);
        if (auto hash = component.getComputedPropertyIndexHash())
          ensureAlive(hash);

        continue;
      }
      case KeyPathPatternComponent::Kind::StoredProperty:
      case KeyPathPatternComponent::Kind::OptionalChain:
      case KeyPathPatternComponent::Kind::OptionalForce:
      case KeyPathPatternComponent::Kind::OptionalWrap:            
        continue;
      }
    }
  }
  
  /// Marks a function as alive if it is not alive yet.
  void ensureAlive(SILFunction *F) {
    if (!isAlive(F))
      makeAlive(F);
  }

  /// Marks a witness table as alive if it is not alive yet.
  void ensureAliveConformance(const ProtocolConformance *C) {
    SILWitnessTable *WT = Module->lookUpWitnessTable(C,
                                                 /*deserializeLazily*/ false);
    if (!WT || isAlive(WT))
      return;
    makeAlive(WT);
  }

  /// Returns true if \a Derived is the same as \p Base or derived from it.
  static bool isDerivedOrEqual(ClassDecl *Derived, ClassDecl *Base) {
    for (;;) {
      if (Derived == Base)
        return true;
      if (!Derived->hasSuperclass())
        break;
      Derived = Derived->getSuperclass()->getClassOrBoundGenericClass();
    }
    return false;
  }

  /// Returns true if the implementation of method \p FD in class \p ImplCl
  /// may be called when the type of the class_method's operand is \p MethodCl.
  /// Both, \p MethodCl and \p ImplCl, may by null if not known or if it's a
  /// protocol method.
  static bool canHaveSameImplementation(FuncDecl *FD, ClassDecl *MethodCl,
                                        ClassDecl *ImplCl) {
    if (!FD || !MethodCl || !ImplCl)
      return true;

    // All implementations of derived classes may be called.
    if (isDerivedOrEqual(ImplCl, MethodCl))
      return true;
    
    // Check if the method implementation is the same in a super class, i.e.
    // it is not overridden in the derived class.
    auto *Impl1 = MethodCl->findImplementingMethod(FD);
    assert(Impl1);
    auto *Impl2 = ImplCl->findImplementingMethod(FD);
    assert(Impl2);
    
    return Impl1 == Impl2;
  }

  /// Marks the implementing functions of the method \p FD as alive. If it is a
  /// class method, \p MethodCl is the type of the class_method instruction's
  /// operand.
  void ensureAliveClassMethod(MethodInfo *mi, FuncDecl *FD, ClassDecl *MethodCl) {
    if (mi->methodIsCalled)
      return;
    bool allImplsAreCalled = true;

    for (FuncImpl &FImpl : mi->implementingFunctions) {
      if (!isAlive(FImpl.F) &&
          canHaveSameImplementation(FD, MethodCl, FImpl.Impl.Cl)) {
        makeAlive(FImpl.F);
      } else {
        allImplsAreCalled = false;
      }
    }
    if (allImplsAreCalled)
      mi->methodIsCalled = true;
  }

  /// Marks the implementing functions of the protocol method \p mi as alive.
  void ensureAliveProtocolMethod(MethodInfo *mi) {
    assert(mi->isWitnessMethod);
    if (mi->methodIsCalled)
      return;
    mi->methodIsCalled = true;
    for (FuncImpl &FImpl : mi->implementingFunctions) {
      if (FImpl.Impl.Conf) {
        SILWitnessTable *WT = Module->lookUpWitnessTable(FImpl.Impl.Conf,
                                                  /*deserializeLazily*/ false);
        if (!WT || isAlive(WT))
          makeAlive(FImpl.F);
      } else {
        makeAlive(FImpl.F);
      }
    }
  }

  /// Gets the base implementation of a method.
  /// We always use the most overridden function to describe a method.
  AbstractFunctionDecl *getBase(AbstractFunctionDecl *FD) {
    while (FD->getOverriddenDecl()) {
      FD = FD->getOverriddenDecl();
    }
    return FD;
  }

  /// Scans all references inside a function.
  void scanFunction(SILFunction *F) {
    // Don't scan functions that are not going to be SIL serialized or emitted
    // by IRGen, because they do not keep anything alive.
    // FIXME: It does not make any sense to scan functions that are not going to
    // be serialized or emitted. But if we don't do it here, then some of the
    // functions that they call are going to be marked as alive and will be
    // removed, even though they are referenced from these non-serialized or
    // non-emitted functions. I.e. a removed function may be referenced from a
    // non-removed one.

    // if (!shouldBeSerializedOrEmitted(F))
    //  return;

    DEBUG(llvm::dbgs() << "    scan function " << F->getName() << '\n');

    // First scan all instructions of the function.
    for (SILBasicBlock &BB : *F) {
      for (SILInstruction &I : BB) {
        if (!shouldSkipIndirectMethodInvocations()) {
          if (auto *WMI = dyn_cast<WitnessMethodInst>(&I)) {
            auto *funcDecl =
                cast<AbstractFunctionDecl>(WMI->getMember().getDecl());
            assert(funcDecl == getBase(funcDecl));
            MethodInfo *mi = getMethodInfo(funcDecl, /*isWitnessTable*/ true);
            ensureAliveProtocolMethod(mi);
          } else if (auto *MI = dyn_cast<MethodInst>(&I)) {
            auto *funcDecl =
                getBase(cast<AbstractFunctionDecl>(MI->getMember().getDecl()));
            assert(MI->getNumOperands() - MI->getNumTypeDependentOperands() ==
                       1 &&
                   "method insts except witness_method must have 1 operand");
            ClassDecl *MethodCl =
                MI->getOperand(0)->getType().getClassOrBoundGenericClass();
            MethodInfo *mi = getMethodInfo(funcDecl, /*isWitnessTable*/ false);
            ensureAliveClassMethod(mi, dyn_cast<FuncDecl>(funcDecl), MethodCl);
          }
        }
        if (auto *FRI = dyn_cast<FunctionRefInst>(&I)) {
          ensureAlive(FRI->getReferencedFunction());
        } else if (auto *KPI = dyn_cast<KeyPathInst>(&I)) {
          ensureKeyPathComponentsAreAlive(KPI->getPattern());
        }
      }
    }
  }

  /// Retrieve the visibility information from the AST.
  bool isVisibleExternally(const ValueDecl *decl) {
    AccessLevel access = decl->getEffectiveAccess();
    SILLinkage linkage;
    switch (access) {
    case AccessLevel::Private:
    case AccessLevel::FilePrivate:
      linkage = SILLinkage::Private;
      break;
    case AccessLevel::Internal:
      linkage = SILLinkage::Hidden;
      break;
    case AccessLevel::Public:
    case AccessLevel::Open:
      linkage = SILLinkage::Public;
      break;
    }
    if (isPossiblyUsedExternally(linkage, Module->isWholeModule()))
      return true;

    // If a vtable or witness table (method) is only visible in another module
    // it can be accessed inside that module and we don't see this access.
    // We hit this case e.g. if a table is imported from the stdlib.
    if (decl->getDeclContext()->getParentModule() != Module->getSwiftModule())
      return true;

    return false;
  }

  /// Find anchors in vtables and witness tables, if required.
  virtual void findAnchorsInTables() = 0;

  /// Find all functions which are alive from the beginning.
  /// For example, functions which may be referenced externally.
  void findAnchors() {

    findAnchorsInTables();

    for (SILFunction &F : *Module) {
      if (isAnchorFunction(&F)) {
        DEBUG(llvm::dbgs() << "  anchor function: " << F.getName() << "\n");
        ensureAlive(&F);
      }

      if (!F.shouldOptimize()) {
        DEBUG(llvm::dbgs() << "  anchor a no optimization function: " << F.getName() << "\n");
        ensureAlive(&F);
      }
    }
  }

public:
  FunctionLivenessComputation(SILModule *module) :
    Module(module) {}

  /// The main entry point of the optimization.
  bool findAliveFunctions() {

    DEBUG(llvm::dbgs() << "running function elimination\n");

    // Find everything which may not be eliminated, e.g. because it is accessed
    // externally.
    findAnchors();

    // The core of the algorithm: Mark functions as alive which can be reached
    // from the anchors.
    while (!Worklist.empty()) {
      SILFunction *F = Worklist.back();
      Worklist.pop_back();
      scanFunction(F);
    }

    return false;
  }

  virtual ~FunctionLivenessComputation() {}
};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
//                             DeadFunctionElimination
//===----------------------------------------------------------------------===//

namespace {

class DeadFunctionElimination : FunctionLivenessComputation {

  void collectMethodImplementations() {
    // Collect vtable method implementations.
    for (SILVTable &vTable : Module->getVTableList()) {
      for (const SILVTable::Entry &entry : vTable.getEntries()) {
        // We don't need to collect destructors because we mark them as alive
        // anyway.
        if (entry.Method.kind == SILDeclRef::Kind::Deallocator ||
            entry.Method.kind == SILDeclRef::Kind::IVarDestroyer) {
          continue;
        }
        SILFunction *F = entry.Implementation;
        auto *fd = getBase(cast<AbstractFunctionDecl>(entry.Method.getDecl()));
        MethodInfo *mi = getMethodInfo(fd, /*isWitnessTable*/ false);
        mi->addClassMethodImpl(F, vTable.getClass());
      }
    }

    // Collect witness method implementations.
    for (SILWitnessTable &WT : Module->getWitnessTableList()) {
      ProtocolConformance *Conf = WT.getConformance();
      for (const SILWitnessTable::Entry &entry : WT.getEntries()) {
        if (entry.getKind() != SILWitnessTable::Method)
          continue;

        auto methodWitness = entry.getMethodWitness();
        auto *fd = cast<AbstractFunctionDecl>(methodWitness.Requirement.
                                              getDecl());
        assert(fd == getBase(fd) && "key in witness table is overridden");
        SILFunction *F = methodWitness.Witness;
        if (!F)
          continue;

        MethodInfo *mi = getMethodInfo(fd, /*isWitnessTable*/ true);
        mi->addWitnessFunction(F, Conf);
      }
    }

    // Collect default witness method implementations.
    for (SILDefaultWitnessTable &WT : Module->getDefaultWitnessTableList()) {
      for (const SILDefaultWitnessTable::Entry &entry : WT.getEntries()) {
        if (!entry.isValid())
          continue;

        SILFunction *F = entry.getWitness();
        auto *fd = cast<AbstractFunctionDecl>(entry.getRequirement().getDecl());
        MethodInfo *mi = getMethodInfo(fd, /*isWitnessTable*/ true);
        mi->addWitnessFunction(F, nullptr);
      }
    }
    

  }

  /// DeadFunctionElimination pass takes functions
  /// reachable via vtables and witness_tables into account
  /// when computing a function liveness information.
  void findAnchorsInTables() override {

    collectMethodImplementations();

    // Check vtable methods.
    for (SILVTable &vTable : Module->getVTableList()) {
      for (const SILVTable::Entry &entry : vTable.getEntries()) {
        if (entry.Method.kind == SILDeclRef::Kind::Deallocator ||
            entry.Method.kind == SILDeclRef::Kind::IVarDestroyer) {
          // Destructors are alive because they are called from swift_release
          ensureAlive(entry.Implementation);
          continue;
        }

        SILFunction *F = entry.Implementation;
        auto *fd = getBase(cast<AbstractFunctionDecl>(entry.Method.getDecl()));

        if (// A conservative approach: if any of the overridden functions is
            // visible externally, we mark the whole method as alive.
            isPossiblyUsedExternally(entry.Linkage, Module->isWholeModule())
            // We also have to check the method declaration's access level.
            // Needed if it's a public base method declared in another
            // compilation unit (for this we have no SILFunction).
            || isVisibleExternally(fd)
            // Declarations are always accessible externally, so they are alive.
            || !F->isDefinition()) {
          MethodInfo *mi = getMethodInfo(fd, /*isWitnessTable*/ false);
          ensureAliveClassMethod(mi, nullptr, nullptr);
        }
      }
    }

    // Check witness table methods.
    for (SILWitnessTable &WT : Module->getWitnessTableList()) {
      ProtocolConformance *Conf = WT.getConformance();
      if (isVisibleExternally(Conf->getProtocol())) {
        // The witness table is visible from "outside". Therefore all methods
        // might be called and we mark all methods as alive.
        for (const SILWitnessTable::Entry &entry : WT.getEntries()) {
          if (entry.getKind() != SILWitnessTable::Method)
            continue;

          auto methodWitness = entry.getMethodWitness();
          auto *fd = cast<AbstractFunctionDecl>(methodWitness.Requirement.
                                                getDecl());
          assert(fd == getBase(fd) && "key in witness table is overridden");
          SILFunction *F = methodWitness.Witness;
          if (!F)
            continue;

          MethodInfo *mi = getMethodInfo(fd, /*isWitnessTable*/ true);
          ensureAliveProtocolMethod(mi);
        }
      }

      // We don't do dead witness table elimination right now. So we assume
      // that all witness tables are alive. Dead witness table elimination is
      // done in IRGen by lazily emitting witness tables.
      makeAlive(&WT);
    }

    // Check default witness methods.
    for (SILDefaultWitnessTable &WT : Module->getDefaultWitnessTableList()) {
      if (isVisibleExternally(WT.getProtocol())) {
        // The default witness table is visible from "outside". Therefore all
        // methods might be called and we mark all methods as alive.
        for (const SILDefaultWitnessTable::Entry &entry : WT.getEntries()) {
          if (!entry.isValid())
            continue;

          auto *fd =
              cast<AbstractFunctionDecl>(entry.getRequirement().getDecl());
          assert(fd == getBase(fd) &&
                 "key in default witness table is overridden");
          SILFunction *F = entry.getWitness();
          if (!F)
            continue;

          MethodInfo *mi = getMethodInfo(fd, /*isWitnessTable*/ true);
          ensureAliveProtocolMethod(mi);
        }
      }
    }
  }

  /// Removes all dead methods from vtables and witness tables.
  bool removeDeadEntriesFromTables() {
    bool changedTable = false;
    for (SILVTable &vTable : Module->getVTableList()) {
      vTable.removeEntries_if([this, &changedTable]
                              (SILVTable::Entry &entry) -> bool {
        if (!isAlive(entry.Implementation)) {
          DEBUG(llvm::dbgs() << "  erase dead vtable method " <<
                entry.Implementation->getName() << "\n");
          changedTable = true;
          return true;
        }
        return false;
      });
    }

    auto &WitnessTables = Module->getWitnessTableList();
    for (auto WI = WitnessTables.begin(), EI = WitnessTables.end(); WI != EI;) {
      SILWitnessTable *WT = &*WI;
      WI++;
      WT->clearMethods_if([this, &changedTable]
                          (const SILWitnessTable::MethodWitness &MW) -> bool {
        if (!isAlive(MW.Witness)) {
          DEBUG(llvm::dbgs() << "  erase dead witness method " <<
                MW.Witness->getName() << "\n");
          changedTable = true;
          return true;
        }
        return false;
      });
    }

    auto DefaultWitnessTables = Module->getDefaultWitnessTables();
    for (auto WI = DefaultWitnessTables.begin(),
              EI = DefaultWitnessTables.end();
         WI != EI;) {
      SILDefaultWitnessTable *WT = &*WI;
      WI++;
      WT->clearMethods_if([this, &changedTable](SILFunction *MW) -> bool {
        if (!MW)
          return false;
        if (!isAlive(MW)) {
          DEBUG(llvm::dbgs() << "  erase dead default witness method "
                             << MW->getName() << "\n");
          changedTable = true;
          return true;
        }
        return false;
      });
    }
    return changedTable;
  }

public:
  DeadFunctionElimination(SILModule *module)
      : FunctionLivenessComputation(module) {}

  /// The main entry point of the optimization.
  void eliminateFunctions(SILModuleTransform *DFEPass) {

    DEBUG(llvm::dbgs() << "running dead function elimination\n");
    findAliveFunctions();

    bool changedTables = removeDeadEntriesFromTables();

    // First drop all references so that we don't get problems with non-zero
    // reference counts of dead functions.
    std::vector<SILFunction *> DeadFunctions;
    for (SILFunction &F : *Module) {
      if (!isAlive(&F)) {
        F.dropAllReferences();
        DeadFunctions.push_back(&F);
      }
    }

    // Next step: delete dead witness tables.
    SILModule::WitnessTableListType &WTables = Module->getWitnessTableList();
    for (auto Iter = WTables.begin(), End = WTables.end(); Iter != End;) {
      SILWitnessTable *Wt = &*Iter;
      Iter++;
      if (!isAlive(Wt)) {
        DEBUG(llvm::dbgs() << "  erase dead witness table " << Wt->getName()
                           << '\n');
        Module->deleteWitnessTable(Wt);
      }
    }

    // Last step: delete all dead functions.
    while (!DeadFunctions.empty()) {
      SILFunction *F = DeadFunctions.back();
      DeadFunctions.pop_back();

      DEBUG(llvm::dbgs() << "  erase dead function " << F->getName() << "\n");
      NumDeadFunc++;
      DFEPass->notifyDeleteFunction(F);
      Module->eraseFunction(F);
    }
    if (changedTables)
      DFEPass->invalidateFunctionTables();
  }
};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
//                        ExternalFunctionDefinitionsElimination
//===----------------------------------------------------------------------===//

namespace {

/// This pass performs removal of external function definitions for a sake of
/// reducing the amount of code to run through IRGen. It is supposed to run very
/// late in the pipeline, after devirtualization, inlining and specialization
/// passes.
///
/// NOTE:
/// Overall, this pass does not try to remove any information which can be
/// useful for LLVM code generation, e.g. for analysis of function's
/// side-effects. Therefore it does not remove bodies of any external functions
/// that are alive, because LLVM may analyze their bodies to determine their
/// side-effects and use it to achieve a better optimization.
///
/// Current implementation does not consider functions which are reachable only
/// via vtables or witness_tables as alive and removes their bodies, because
/// even if they would be kept around, LLVM does not know how to look at
/// function definitions through Swift's vtables and witness_tables.
///
/// TODO:
/// Once there is a proper support for IPO in Swift compiler and/or there is
/// a way to communicate function's side-effects without providing its body
/// (e.g. by means of SILFunction flags, attributes, etc), it should be
/// safe to remove bodies of all external definitions.

class ExternalFunctionDefinitionsElimination : FunctionLivenessComputation {

  /// ExternalFunctionDefinitionsElimination pass does not take functions
  /// reachable via vtables and witness_tables into account when computing
  /// a function liveness information. The only exceptions are external
  /// transparent functions, because bodies of external transparent functions
  /// should never be removed.
  void findAnchorsInTables() override {
    // Check vtable methods.
    for (SILVTable &vTable : Module->getVTableList()) {
      for (auto &entry : vTable.getEntries()) {
        SILFunction *F = entry.Implementation;
        if (F->isTransparent() && isAvailableExternally(F->getLinkage()))
          ensureAlive(F);
      }
    }

    // Check witness methods.
    for (SILWitnessTable &WT : Module->getWitnessTableList()) {
      isVisibleExternally(WT.getConformance()->getProtocol());
      for (const SILWitnessTable::Entry &entry : WT.getEntries()) {
        if (entry.getKind() != SILWitnessTable::Method)
          continue;

        auto methodWitness = entry.getMethodWitness();
        SILFunction *F = methodWitness.Witness;
        if (!F)
          continue;
        if (F->isTransparent() && isAvailableExternally(F->getLinkage()))
          ensureAlive(F);
      }
    }

    // Check default witness methods.
    for (SILDefaultWitnessTable &WT : Module->getDefaultWitnessTableList()) {
      for (const SILDefaultWitnessTable::Entry &entry : WT.getEntries()) {
        if (!entry.isValid())
          continue;

        SILFunction *F = entry.getWitness();
        if (F->isTransparent() && isAvailableExternally(F->getLinkage()))
          ensureAlive(F);
      }
    }

  }

  bool findAliveFunctions() {
    /// TODO: Once there is a proper support for IPO,
    /// bodies of all external functions can be removed.
    /// Therefore there is no need for a liveness computation.
    /// The next line can be just replaced by:
    /// return false;

    // Keep all transparent functions alive. This is important because we have
    // to generate code for transparent functions.
    // Here we handle the special case if a transparent function is referenced
    // from a non-externally-available function (i.e. a function for which we
    // generate code). And those function is only reachable through a
    // vtable/witness-table. In such a case we would not visit the transparent
    // function in findAliveFunctions() because we don't consider vtables/
    // witness-tables as anchors.
    for (SILFunction &F : *Module) {
      if (isAvailableExternally(F.getLinkage()))
        continue;

      for (SILBasicBlock &BB : F) {
        for (SILInstruction &I : BB) {
          if (auto *FRI = dyn_cast<FunctionRefInst>(&I)) {
            SILFunction *RefF = FRI->getReferencedFunction();
            // FIXME: Bad usage of transparent
            if (RefF->isTransparent() && RefF->isSerialized())
              ensureAlive(RefF);
          }
        }
      }
    }

    return FunctionLivenessComputation::findAliveFunctions();
  }

  /// Try to convert definition into declaration.
  /// Returns true if function was erased from the module.
  bool tryToConvertExternalDefinitionIntoDeclaration(SILFunction *F) {
    // Bail if it is a declaration already
    if (!F->isDefinition())
      return false;
    // Bail if there is no external implementation of this function.
    if (!F->isAvailableExternally())
      return false;
    // Bail if has a shared visibility, as there are no guarantees
    // that an implementation is available elsewhere.
    if (hasSharedVisibility(F->getLinkage()))
      return false;
    // Bail if it does not have a public visibility, as such symbols
    // should not be exposed elsewhere.
    if (!hasPublicVisibility(F->getLinkage())) {
      // Convert into a non-external object?
      //F->setLinkage(SILLinkage::Shared);
      //F->setLinkage(stripExternalFromLinkage(F->getLinkage()));
      return false;
    }
    // Make this definition a declaration by removing the body of a function.

    DEBUG(llvm::dbgs() << "  removed external function " << F->getName()
          << "\n");
    F->dropAllReferences();
    auto &Blocks = F->getBlocks();
    Blocks.clear();
    assert(F->isExternalDeclaration() &&
           "Function should be an external declaration");
    NumEliminatedExternalDefs++;
    return true;
  }

public:
  ExternalFunctionDefinitionsElimination(SILModule *module)
      : FunctionLivenessComputation(module) {}

  /// Eliminate bodies of external functions which are not alive.
  ///
  /// Bodies of alive functions should not be removed, as LLVM may
  /// still need them for analyzing their side-effects.
  void eliminateFunctions(SILModuleTransform *DFEPass) {

    findAliveFunctions();
    // Get rid of definitions for all global functions that are not marked as
    // alive.
    for (auto FI = Module->begin(), EI = Module->end(); FI != EI;) {
      SILFunction *F = &*FI;
      ++FI;
      // Do not remove bodies of any functions that are alive.
      if (!isAlive(F)) {
        if (tryToConvertExternalDefinitionIntoDeclaration(F)) {
          DFEPass->notifyDeleteFunction(F);
          if (F->getRefCount() == 0)
            F->getModule().eraseFunction(F);
        }
      } else if (F->isDefinition() && F->isAvailableExternally() &&
                 !hasSharedVisibility(F->getLinkage()) &&
                 !hasPublicVisibility(F->getLinkage())
                 && !F->getName().startswith("globalinit_")) {
        // Convert into a non-external object so that IRGen emits it?
        //F->setLinkage(SILLinkage::Shared);
      }
    }
  }
};

/// A helper class to mark all alive functions as anchors.
class AliveFunctionsMarker : FunctionLivenessComputation {
  /// AliveFunctionsMarker pass does not take functions
  /// reachable via vtables and witness_tables into account when computing
  /// a function liveness information. The only exceptions are external
  /// transparent functions, because bodies of external transparent functions
  /// should never be removed.
  void findAnchorsInTables() override {
#if 0
    // Check vtable methods.
    for (SILVTable &vTable : Module->getVTableList()) {
      for (auto &entry : vTable.getEntries()) {
        SILFunction *F = entry.Implementation;
        if (F->isTransparent() && isAvailableExternally(F->getLinkage()))
          ensureAlive(F);
      }
    }

    // Check witness methods.
    for (SILWitnessTable &WT : Module->getWitnessTableList()) {
      isVisibleExternally(WT.getConformance()->getProtocol());
      for (const SILWitnessTable::Entry &entry : WT.getEntries()) {
        if (entry.getKind() != SILWitnessTable::Method)
          continue;

        auto methodWitness = entry.getMethodWitness();
        SILFunction *F = methodWitness.Witness;
        if (!F)
          continue;
        if (F->isTransparent() && isAvailableExternally(F->getLinkage()))
          ensureAlive(F);
      }
    }

    // Check default witness methods.
    for (SILDefaultWitnessTable &WT : Module->getDefaultWitnessTableList()) {
      for (const SILDefaultWitnessTable::Entry &entry : WT.getEntries()) {
        if (!entry.isValid())
          continue;

        SILFunction *F = entry.getWitness();
        if (F->isTransparent() && isAvailableExternally(F->getLinkage()))
          ensureAlive(F);
      }
    }
#endif
  }

#if 0
  bool findAliveFunctions() {
    for (SILFunction &F : *Module) {
      if (isAvailableExternally(F.getLinkage()))
        continue;

      for (SILBasicBlock &BB : F) {
        for (SILInstruction &I : BB) {
          if (auto *FRI = dyn_cast<FunctionRefInst>(&I)) {
            SILFunction *RefF = FRI->getReferencedFunction();
            // FIXME: Bad usage of transparent
            if (RefF->isTransparent() && RefF->isSerialized())
              ensureAlive(RefF);
          }
        }
      }
    }

    return FunctionLivenessComputation::findAliveFunctions();
  }
#endif

public:
  AliveFunctionsMarker(SILModule *module)
      : FunctionLivenessComputation(module) {}

  /// Bodies of alive functions should not be removed, as LLVM may
  /// still need them for analyzing their side-effects.
  void markAliveFunctions() {
    // Do not look through indirect method invocations.
    setSkipIndirectMethodInvocations();
    findAliveFunctions();
    // Mark all alive functions as anchors if necessary.
    for (auto FI = Module->begin(), EI = Module->end(); FI != EI;) {
      SILFunction *F = &*FI;
      ++FI;
      if (isAlive(F) && !isAvailableExternally(F->getLinkage())) {
        F->setKeepAsAnchor(true);
      }
    }
  }
};


} // end anonymous namespace

//===----------------------------------------------------------------------===//
//                      Pass Definition and Entry Points
//===----------------------------------------------------------------------===//

namespace {

class SILDeadFuncElimination : public SILModuleTransform {
  void run() override {
    DEBUG(llvm::dbgs() << "Running DeadFuncElimination\n");

    // The deserializer caches functions that it deserializes so that if it is
    // asked to deserialize that function again, it does not do extra work. This
    // causes the function's reference count to be incremented causing it to be
    // alive unnecessarily. We invalidate the SILLoaderCaches here so that we
    // can eliminate such functions.
    getModule()->invalidateSILLoaderCaches();

    DeadFunctionElimination deadFunctionElimination(getModule());
    deadFunctionElimination.eliminateFunctions(this);
  }
  
};

class SILExternalFuncDefinitionsElimination : public SILModuleTransform {
  void run() override {
    DEBUG(llvm::dbgs() << "Running ExternalFunctionDefinitionsElimination\n");

    // The deserializer caches functions that it deserializes so that if it is
    // asked to deserialize that function again, it does not do extra work. This
    // causes the function's reference count to be incremented causing it to be
    // alive unnecessarily. We invalidate the SILLoaderCaches here so that we
    // can eliminate the definitions of such functions.
    getModule()->invalidateSILLoaderCaches();

    ExternalFunctionDefinitionsElimination EFDFE(getModule());
    EFDFE.eliminateFunctions(this);
 }

};

} // end anonymous namespace

SILTransform *swift::createDeadFunctionElimination() {
  return new SILDeadFuncElimination();
}

SILTransform *swift::createExternalFunctionDefinitionsElimination() {
  return new SILExternalFuncDefinitionsElimination();
}

void swift::performSILDeadFunctionElimination(SILModule *M) {
  SILPassManager PM(M);
  llvm::SmallVector<PassKind, 1> Pass = {PassKind::DeadFunctionElimination};
  PM.executePassPipelinePlan(
      SILPassPipelinePlan::getPassPipelineForKinds(Pass));
}

/// \brief Mark all reachable (i.e. currently live) functions from \p M as
/// "public". Here "public" does not mean the SIL linkage, but rather the
/// fact that these functions cannot be eliminated by a dead function
/// elimination any more.
void swift::markAllReachableFunctionsAsAnchors(SILModule *M) {
  AliveFunctionsMarker Marker(M);
  Marker.markAliveFunctions();
}
