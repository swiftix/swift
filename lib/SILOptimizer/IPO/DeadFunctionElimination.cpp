//===--- DeadFunctionElimination.cpp - Eliminate dead functions -----------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2015 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See http://swift.org/LICENSE.txt for license information
// See http://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "sil-dead-function-elimination"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "swift/SILOptimizer/Analysis/SpecializationsAnalysis.h"
#include "swift/SIL/PatternMatch.h"
#include "swift/SIL/Projection.h"
#include "swift/SIL/SILBuilder.h"
#include "swift/SIL/SILVisitor.h"
#include "swift/SILOptimizer/Utils/Local.h"
#include "swift/SILOptimizer/Utils/Generics.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/Debug.h"
using namespace swift;

STATISTIC(NumDeadFunc, "Number of dead functions eliminated");
STATISTIC(NumEliminatedExternalDefs, "Number of external function definitions eliminated");

namespace {

/// This is a base class for passes that are based on function liveness
/// computations like e.g. dead function elimination.
/// It provides a common logic for computing live (i.e. reachable) functions.
class FunctionLivenessComputation {
protected:
  /// Stores which functions implement a vtable or witness table method.
  struct MethodInfo {

    MethodInfo() : isAnchor(false) {}

    /// All functions which implement the method. Together with the class for
    /// which the function implements the method. In case of a witness method,
    /// the class pointer is null.
    SmallVector<std::pair<SILFunction *, ClassDecl *>, 8> implementingFunctions;

    /// True, if the whole method is alive, e.g. because it's class is visible
    /// from outside. This implies that all implementing functions are alive.
    bool isAnchor;
  };

  SILModule *Module;

  SpecializationsAnalysis *SA;

  llvm::DenseMap<AbstractFunctionDecl *, MethodInfo *> MethodInfos;
  llvm::SpecificBumpPtrAllocator<MethodInfo> MethodInfoAllocator;

  llvm::SmallSetVector<SILFunction *, 16> Worklist;

  llvm::SmallPtrSet<SILFunction *, 100> AliveFunctions;

  /// Checks is a function is alive, e.g. because it is visible externally.
  bool isAnchorFunction(SILFunction *F) {

    // Remove internal functions that are not referenced by anything.
    if (isPossiblyUsedExternally(F->getLinkage(), Module->isWholeModule()))
      return true;

    // ObjC functions are called through the runtime and are therefore alive
    // even if not referenced inside SIL.
    if (F->getRepresentation() == SILFunctionTypeRepresentation::ObjCMethod)
      return true;

    // If function is marked as "keep-as-public", don't remove it.
    // Change its linkage to public, so that other applications can refer to it.
    // It is important that this transformation is done at the end of
    // a pipeline, as it may break some optimizations.
    if (F->isKeepAsPublic()) {
      F->setLinkage(SILLinkage::Public);
      F->setFragile(IsFragile_t::IsNotFragile);
      DEBUG(llvm::dbgs() << "DFE: Preserve the specialization "
                         << F->getName() << '\n');
      return true;
    }

    return false;
  }

  /// Gets or creates the MethodInfo for a vtable or witness table method.
  /// \p decl The method declaration. In case of a vtable method this is always
  ///         the most overriden method.
  MethodInfo *getMethodInfo(AbstractFunctionDecl *decl) {
    MethodInfo *&entry = MethodInfos[decl];
    if (entry == nullptr) {
      entry = new (MethodInfoAllocator.Allocate()) MethodInfo();
    }
    return entry;
  }

  /// Adds a function which implements a vtable or witness method. If it's a
  /// vtable method, \p C is the class for which the function implements the
  /// method. For witness methods \C is null.
  void addImplementingFunction(MethodInfo *mi, SILFunction *F, ClassDecl *C) {
    if (mi->isAnchor)
      ensureAlive(F);
    mi->implementingFunctions.push_back(std::make_pair(F, C));
  }

  /// Returns true if a function is marked as alive.
  bool isAlive(SILFunction *F) { return AliveFunctions.count(F) != 0; }

  /// Marks a function as alive.
  void makeAlive(SILFunction *F) {
    AliveFunctions.insert(F);
    assert(F && "function does not exist");
    Worklist.insert(F);
  }

  /// Marks a function as alive if it is not alive yet.
  void ensureAlive(SILFunction *F) {
    if (!isAlive(F))
      makeAlive(F);
  }

  /// Marks a function as alive if it is not alive yet.
  /// Marks everything reachable from it alive as well.
  void ensureAliveRecursively(SILFunction *F) {
    assert(Worklist.empty() && "Worklist should be empty");
    ensureAlive(F);
    while (!Worklist.empty()) {
      SILFunction *F = Worklist.back();
      Worklist.pop_back();
      scanFunction(F);
    }
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
  void ensureAlive(MethodInfo *mi, FuncDecl *FD, ClassDecl *MethodCl) {
    for (auto &Pair : mi->implementingFunctions) {
      SILFunction *FImpl = Pair.first;
      if (!isAlive(FImpl) &&
          canHaveSameImplementation(FD, MethodCl, Pair.second)) {
        makeAlive(FImpl);
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
    for (SILBasicBlock &BB : *F) {
      for (SILInstruction &I : BB) {
        if (auto *MI = dyn_cast<MethodInst>(&I)) {
          auto *funcDecl = getBase(
              cast<AbstractFunctionDecl>(MI->getMember().getDecl()));
          MethodInfo *mi = getMethodInfo(funcDecl);
          ClassDecl *MethodCl = nullptr;
          if (MI->getNumOperands() == 1)
            MethodCl = MI->getOperand(0)->getType(0).getClassOrBoundGenericClass();
          ensureAlive(mi, dyn_cast<FuncDecl>(funcDecl), MethodCl);
        } else if (auto *FRI = dyn_cast<FunctionRefInst>(&I)) {
          ensureAlive(FRI->getReferencedFunction());
        }
      }
    }
  }

  /// Retrieve the visibility information from the AST.
  bool isVisibleExternally(ValueDecl *decl) {
    Accessibility accessibility = decl->getEffectiveAccess();
    SILLinkage linkage;
    switch (accessibility) {
    case Accessibility::Private:
      linkage = SILLinkage::Private;
      break;
    case Accessibility::Internal:
      linkage = SILLinkage::Hidden;
      break;
    case Accessibility::Public:
      linkage = SILLinkage::Public;
      break;
    }
    if (isPossiblyUsedExternally(linkage, Module->isWholeModule()))
      return true;

    // If a vtable or witness table (method) is only visible in another module
    // it can be accessed inside that module and we don't see this access.
    // We hit this case e.g. if a table is imported from the stdlib.
    if (decl->getDeclContext()->getParentModule() !=
        Module->getAssociatedContext()->getParentModule())
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
    }

    for (SILGlobalVariable &G : Module->getSILGlobalList()) {
      if (SILFunction *initFunc = G.getInitializer()) {
        ensureAlive(initFunc);
      }
    }
  }

public:
  FunctionLivenessComputation(SILModule *module, SpecializationsAnalysis *SA) :
    Module(module), SA(SA) {}

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

 void countLiveSpecializations(SILModuleTransform *ST);

 virtual ~FunctionLivenessComputation() {}
};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
//                             DeadFunctionElimination
//===----------------------------------------------------------------------===//

namespace {

class DeadFunctionElimination : public FunctionLivenessComputation {

  /// DeadFunctionElimination pass takes functions
  /// reachable via vtables and witness_tables into account
  /// when computing a function liveness information.
  void findAnchorsInTables() {
    // Check vtable methods.
    for (SILVTable &vTable : Module->getVTableList()) {
      for (auto &entry : vTable.getEntries()) {
        // Destructors are alive because they are called from swift_release
        if (entry.first.kind == SILDeclRef::Kind::Deallocator ||
            entry.first.kind == SILDeclRef::Kind::IVarDestroyer) {
          ensureAlive(entry.second);
          continue;
        }

        SILFunction *F = entry.second;
        auto *fd = cast<AbstractFunctionDecl>(entry.first.getDecl());
        fd = getBase(fd);
        MethodInfo *mi = getMethodInfo(fd);
        addImplementingFunction(mi, F, vTable.getClass());

        if (// A conservative approach: if any of the overridden functions is
            // visible externally, we mark the whole method as alive.
            isPossiblyUsedExternally(F->getLinkage(), Module->isWholeModule())
            // We also have to check the method declaration's accessibility.
            // Needed if it's a public base method declared in another
            // compilation unit (for this we have no SILFunction).
            || isVisibleExternally(fd)
            // Declarations are always accessible externally, so they are alive.
            || !F->isDefinition()) {
          ensureAlive(mi, nullptr, nullptr);
        }
      }
    }

    // Check witness methods.
    for (SILWitnessTable &WT : Module->getWitnessTableList()) {
      bool tableIsAlive = isVisibleExternally(WT.getConformance()->getProtocol());
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

        MethodInfo *mi = getMethodInfo(fd);
        addImplementingFunction(mi, F, nullptr);
        if (tableIsAlive || !F->isDefinition())
          ensureAlive(mi, nullptr, nullptr);
      }
    }
  }

  /// Removes all dead methods from vtables and witness tables.
  void removeDeadEntriesFromTables() {
    for (SILVTable &vTable : Module->getVTableList()) {
      vTable.removeEntries_if([this](SILVTable::Pair &entry) -> bool {
        if (!isAlive(entry.second)) {
          DEBUG(llvm::dbgs() << "  erase dead vtable method " <<
                entry.second->getName() << "\n");
          return true;
        }
        return false;
      });
    }

    auto &WitnessTables = Module->getWitnessTableList();
    for (auto WI = WitnessTables.begin(), EI = WitnessTables.end(); WI != EI;) {
      SILWitnessTable *WT = &*WI;
      WI++;
      WT->clearMethods_if([this](const SILWitnessTable::MethodWitness &MW) -> bool {
        if (!isAlive(MW.Witness)) {
          DEBUG(llvm::dbgs() << "  erase dead witness method " <<
                MW.Witness->getName() << "\n");
          return true;
        }
        return false;
      });
    }
  }

public:
  DeadFunctionElimination(SILModule *module, SpecializationsAnalysis *SA)
      : FunctionLivenessComputation(module, SA) {}

  /// The main entry point of the optimization.
  void eliminateFunctions(SILModuleTransform *DFEPass) {

    DEBUG(llvm::dbgs() << "running dead function elimination\n");
    findAliveFunctions();

    removeDeadEntriesFromTables();

    // Unregister all dead specializations.
    for (SILFunction &F : *Module) {
      if (!isAlive(&F))
        SA->getOrBuildSpecializationsInfo().unregisterSpecialization(&F);
    }

    // Mark all generic functions that still have live specializations as alive.
    for (SILFunction &F : *Module) {
      if (!isAlive(&F)) {
        if (SA->getOrBuildSpecializationsInfo().
                getSpecializations(F.getName()).size() >= 1)
          ensureAliveRecursively(&F);
      }
    }

    // Update the sharing attribute of SILFunctions having it, if necessary.
    // If the original function picked as the "sharing" is removed by the
    // dead function elimination (or elsewhere), try to find another one,
    // which is still around.
    for (SILFunction &F : *Module) {
      if (!isAlive(&F))
        continue;

      if (!F.getSharing())
        continue;

      auto *SF = F.getSharing();
      if (isAlive(SF)) {
        llvm::dbgs() << "Specialization is still alive after DFE (1): " << F.getName() << '\n';
        continue;
      }

      // The original sharing specialization function was removed.
      // Try to find another one with a compatible layout and alive.
      auto &SI = SA->getOrBuildSpecializationsInfo();
      auto &SpecInfo = SI.getSpecializationInfo(&F);
      auto GenericName = SI.getGenericFunction(&F);
      llvm::dbgs() << "Generic name is: " << GenericName << "\n";
      auto *GenericF = Module->lookUpFunction(GenericName);
      assert(GenericF && "Generic function should be alive");
      SF = SI.findSpecialization(*Module, GenericF, SpecInfo.getSubstitutions());
      F.setSharing(SF);
      if (SF)
        llvm::dbgs() << "Specialization is still alive after DFE (2): " << F.getName() << '\n';
      else {
        llvm::dbgs() << "Specialization is still alive after DFE (3), but not shared anymore: " << F.getName() << '\n';
      }
    }

    // First drop all references so that we don't get problems with non-zero
    // reference counts of dead functions.
    for (SILFunction &F : *Module)
      if (!isAlive(&F))
        F.dropAllReferences();

    // Next step: delete all dead functions.
    bool NeedUpdate = false;
    for (auto FI = Module->begin(), EI = Module->end(); FI != EI;) {
      SILFunction *F = &*FI;
      ++FI;
      if (!isAlive(F)) {
        DEBUG(llvm::dbgs() << "  erase dead function " << F->getName() << "\n");
        NumDeadFunc++;
        Module->eraseFunction(F);
        NeedUpdate = true;
        DFEPass->invalidateAnalysis(F, SILAnalysis::InvalidationKind::Everything);
      }
    }
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

class ExternalFunctionDefinitionsElimination : public FunctionLivenessComputation {

  /// ExternalFunctionDefinitionsElimination pass does not take functions
  /// reachable via vtables and witness_tables into account when computing
  /// a function liveness information.
  void findAnchorsInTables() {
  }

  bool findAliveFunctions() {
    /// TODO: Once there is a proper support for IPO,
    /// bodies of all external functions can be removed.
    /// Therefore there is no need for a livesness computation.
    /// The next line can be just replaced by:
    /// return false;
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
    // Make this definition a declaration by removing the body of a function.

    DEBUG(llvm::dbgs() << "  removed external function " << F->getName()
          << "\n");
    F->dropAllReferences();
    auto &Blocks = F->getBlocks();
    Blocks.clear();
    assert(F->isExternalDeclaration() &&
           "Function should be an external declaration");
    if (F->getRefCount() == 0)
      F->getModule().eraseFunction(F);

    NumEliminatedExternalDefs++;
    return true;
  }

public:
  ExternalFunctionDefinitionsElimination(SILModule *module,
										 SpecializationsAnalysis *SA)
      : FunctionLivenessComputation(module, SA) {}

  /// Eliminate bodies of external functions which are not alive.
  ///
  /// Bodies of alive functions should not be removed, as LLVM may
  /// still need them for analyzing their side-effects.
  void eliminateFunctions(SILModuleTransform *DFEPass) {

    findAliveFunctions();


    // Unregister all dead specializations.
    for (SILFunction &F : *Module) {
      if (!isAlive(&F))
        SA->getOrBuildSpecializationsInfo().unregisterSpecialization(&F);
    }

    // Mark all generic functions that still have live specializations as alive.
    for (SILFunction &F : *Module) {
      if (!isAlive(&F)) {
        if (SA->getOrBuildSpecializationsInfo().
                getSpecializations(F.getName()).size() >= 1)
          ensureAliveRecursively(&F);
      }
    }

    // Get rid of definitions for all global functions that are not marked as
    // alive.
    bool NeedUpdate = false;
    for (auto FI = Module->begin(), EI = Module->end(); FI != EI;) {
      SILFunction *F = &*FI;
      ++FI;
      // Do not remove bodies of any functions that are alive.
      if (!isAlive(F)) {
        if (tryToConvertExternalDefinitionIntoDeclaration(F)) {
          NeedUpdate = true;
          DFEPass->invalidateAnalysis(F,
                                    SILAnalysis::InvalidationKind::Everything);
        }
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
	auto *SA = getAnalysis<SpecializationsAnalysis>();

    DEBUG(llvm::dbgs() << "Running DeadFuncElimination\n");

    // The deserializer caches functions that it deserializes so that if it is
    // asked to deserialize that function again, it does not do extra work. This
    // causes the function's reference count to be incremented causing it to be
    // alive unnecessarily. We invalidate the SILLoaderCaches here so that we
    // can eliminate such functions.
    getModule()->invalidateSILLoaderCaches();

    DeadFunctionElimination deadFunctionElimination(getModule(), SA);
    deadFunctionElimination.eliminateFunctions(this);
	deadFunctionElimination.countLiveSpecializations(this);
  }

  StringRef getName() override { return "Dead Function Elimination"; }
};

class SILExternalFuncDefinitionsElimination : public SILModuleTransform {
  void run() override {
	auto *SA = getAnalysis<SpecializationsAnalysis>();

    DEBUG(llvm::dbgs() << "Running ExternalFunctionDefinitionsElimination\n");

    // The deserializer caches functions that it deserializes so that if it is
    // asked to deserialize that function again, it does not do extra work. This
    // causes the function's reference count to be incremented causing it to be
    // alive unnecessarily. We invalidate the SILLoaderCaches here so that we
    // can eliminate the definitions of such functions.
    getModule()->invalidateSILLoaderCaches();

    ExternalFunctionDefinitionsElimination EFDFE(getModule(), SA);
    EFDFE.eliminateFunctions(this);
    EFDFE.countLiveSpecializations(this);
 }

  StringRef getName() override {
    return "External Function Definitions Elimination";
  }
};

} // end anonymous namespace

unsigned getFunctionSize(SILFunction *F) {
  unsigned size = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++size;
  return size;
}

/// This is a temporary hack to collect information about potentially
/// sharable specializations.
void FunctionLivenessComputation::countLiveSpecializations(SILModuleTransform *ST) {
  return;
  auto &SI = SA->getOrBuildSpecializationsInfo();
  unsigned GenericsSize = 0;
  unsigned SpecializationsCount = 0;
  unsigned GenericsCount = 0;
  unsigned MergableGenericsCount = 0;
  unsigned MergableSpecializationsCount = 0;
  unsigned MergableSpecializationsSize = 0;
  unsigned MergableGenericsSize = 0;
  unsigned SpecializedSize = 0;
  unsigned TotalSize = 0;

  for (auto &F : *Module) {
    unsigned Size = getFunctionSize(&F);
    TotalSize += Size;
    auto GenericName = SI.getGenericFunction(&F);
    if (GenericName.empty())
      continue;
    SpecializedSize += Size;
    SpecializationsCount++;
    if (SI.getSpecializations(GenericName).size() >= 2) {
      MergableSpecializationsCount++;
      MergableSpecializationsSize += Size;
    }
  }


  bool NeedsUpdate = false;
  auto &Specializations = SI.getSpeicalizedGenerics();
  SmallVector<SILFunction *, 32> FunctionsToRemove;
  SmallVector<SILFunction *, 32> SpecializationsToRemove;
  for (auto &Pair : Specializations) {
    auto *F = Module->lookUpFunction(Pair.getKey());
    // ???
    assert(F && "Generic function should exist");
    if (!F)
      continue;
    unsigned Size = getFunctionSize(F);
    GenericsCount++;
    GenericsSize += Size;
    if (Pair.getValue().size() >= 2) {
      MergableGenericsCount++;
      MergableGenericsSize += Size;
    }

    if (F->getRefCount() == 0 && Pair.getValue().size() == 1) {
      auto Specialization = Module->lookUpFunction(*Pair.getValue().begin());
      //assert(Specialization && "Specialization should exist");
      if (Specialization)
        SpecializationsToRemove.push_back(Specialization);
      else {
        StringRef Name = *Pair.getValue().begin();
        llvm::dbgs() << "Unknown specialization: " << Name << "\n";
        assert(false && "Unknown specialization");
//        SI.unregisterSpecialization(Pair.getValue().begin()->getFunctionName());
//        SI.getSpecializations(Pair.second.begin()->getFunctionName());
      }

      if (!isAlive(F))
        FunctionsToRemove.push_back(F);
      NeedsUpdate = true;
    }
  }

  if (NeedsUpdate) {
    // First, remove all pending specializations.
    for (auto F : SpecializationsToRemove) {
       SI.unregisterSpecialization(F);
    }
#if 0
    auto *CG = CGA->getCallGraphOrNull();
    // First, drop all references
    for (auto F : FunctionsToRemove) {
      CallGraphEditor(CG).removeAllCalleeEdgesFrom(F);
      F->dropAllReferences();
      SI.unregisterGeneric(F);
    }

    // Then, remove all pending generic functions.
    for (auto F : FunctionsToRemove) {
      Module->eraseFunction(F);
      CallGraphEditor(CG).removeCallGraphNode(F);
      CGA->lockInvalidation();
      ST->invalidateAnalysis(F, SILAnalysis::PreserveKind::Nothing);
      CGA->unlockInvalidation();
    }

    CallGraphEditor(CG).updateCalleeSets();
#endif
  }

  // Total amount of SIL instructions saved by sharing.
  unsigned SavedSize = 0;

  // Now try to see which specializations can be shared.
  for (auto &Pair : Specializations) {
    auto GenericName = Pair.getKey();
    auto *GenericF = Module->lookUpFunction(GenericName);
    // Set of specializations for the current generic.
    auto Specs = Pair.getValue();
    auto &GI = SI.getGenericInfo(GenericF);
    auto SharingKind = GI.getSpecializationSharingKind(SI);

    // Bail if specializations of a given generic cannot be shared.
    // This may happen e.g. if their implementations depend on
    // methods from its requirements.
    if (SharingKind == NoSharing)
      continue;

    if (SharingKind == LayoutIndependentSharing) {
      //  Nothing to share.
      if (Specs.size() < 2)
        continue;
      // All its specializations can be shared.
      // TODO: Should we group them into class-based and non-class based?
      // TODO: Should we group them into RC-based and non-RC-based?
      llvm::dbgs() << "\n\nGeneric function " << GenericName << " is generic type layout independent.\n";
      llvm::dbgs() << "All its specializations can be shared:\n";
      for (auto &S : Specs) {
        llvm::dbgs() << "\t" << S << "\n";
        auto Size = getFunctionSize(Module->lookUpFunction(S));
        SavedSize += Size;
        llvm::dbgs() << "Saved specialization size: " << Size << "\n";
      }

      // Output the generic function whose specialization is shared.
      llvm::dbgs() << "One of specializations is:\n";
      Module->lookUpFunction(Specs[0])->dump();
      llvm::dbgs() << "\n\nGeneric function is:\n";
      GenericF->dump();
    }

    if (SharingKind == LayoutDependentSharing) {
      // Maps a specialization to the specialization it can be shared with.
      llvm::StringMap<StringRef> CanBeShared;

      // Find specializations with compatible layouts.
      for (int i = 0, e = Specs.size(); i < e; ++i) {
        unsigned LayoutDependentSharedSpecsNum = 0;
        auto &CurSpecName = Specs[i];
        // If it is shared already, no need to analyze it.
        if (CanBeShared.count(CurSpecName))
          continue;
        auto &CurSpecInfo = SI.getSpecializationInfo(CurSpecName);
        CanBeShared[CurSpecName] = CurSpecName;
        for (int j = i+1; j < e; ++j) {
          auto &SpecName = Specs[j];
          auto &SpecInfo = SI.getSpecializationInfo(SpecName);
          if (SpecInfo.isLayoutCompatibleWith(CurSpecInfo)) {
            CanBeShared[SpecName] = CurSpecName;
            LayoutDependentSharedSpecsNum++;
            llvm::dbgs() << "\n\nSpecialization:  " << CurSpecName << " is layout compatible with:\n\n";
            llvm::dbgs() << "Specialization:  " << SpecName << " and can be shared \n";
#if 0
            llvm::dbgs() << "Number of generic parameters: " << SpecInfo.getSubstitutions().size() << "\n";
            llvm::dbgs() << "Number of generic layouts: " << SpecInfo.getLayouts().size() << "\n";
            for (int k = 0, ke = SpecInfo.getLayouts().size(); k < ke; ++k) {
              llvm::dbgs() << "\tLayout1: (" << CurSpecInfo.getLayouts()[k] << ") Layout2: (" << SpecInfo.getLayouts()[k] << ")\n";
            }
#endif
            auto Size = getFunctionSize(Module->lookUpFunction(SpecName));
            SavedSize += Size;
            llvm::dbgs() << "Saved specialization size: " << Size << "\n";
          }
        }
        // Output the generic function whose specialization is shared.
        if (LayoutDependentSharedSpecsNum)
          Module->lookUpFunction(Specs[i])->dump();
      }
    }
  }

  llvm::dbgs() << "\n\nNumber of live specializations: " << SpecializationsCount << "\n";
  llvm::dbgs() << "Number of mergable live specializations: " << MergableSpecializationsCount << "\n";
  llvm::dbgs() << "Number of specialized generics: " << GenericsCount << "\n";
  llvm::dbgs() << "Number of mergable specialized generics: " << MergableGenericsCount << "\n";

  llvm::dbgs() << "Size of mergable live specializations: " << MergableSpecializationsSize << "\n";
  llvm::dbgs() << "Size of all live specializations: " << SpecializedSize << "\n";
  llvm::dbgs() << "Size of all functions: " << TotalSize << "\n";
  llvm::dbgs() << "Size of mergable specialized generics: " << MergableGenericsSize << "\n";
  llvm::dbgs() << "Size of all specialized generics: " << GenericsSize << "\n";
  llvm::dbgs() << "\n\nTotal saved specialization size: " << SavedSize << "\n";
}

SILTransform *swift::createDeadFunctionElimination() {
  return new SILDeadFuncElimination();
}

SILTransform *swift::createExternalFunctionDefinitionsElimination() {
  return new SILExternalFuncDefinitionsElimination();
}
