//===--- Link.cpp - Link in transparent SILFunctions from module ----------===//
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
#define DEBUG_TYPE "sil-link"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "swift/AST/ProtocolConformance.h"
#include "swift/SIL/SILArgument.h"
#include "swift/SIL/SILModule.h"

using namespace swift;

//===----------------------------------------------------------------------===//
//                          Top Level Driver
//===----------------------------------------------------------------------===//

void swift::performSILLinking(SILModule *M, bool LinkAll) {
  auto LinkMode = LinkAll? SILModule::LinkingMode::LinkAll :
    SILModule::LinkingMode::LinkNormal;
  for (auto &Fn : *M)
    M->linkFunction(&Fn, LinkMode);

  if (!LinkAll)
    return;

  M->linkAllWitnessTables();
  M->linkAllVTables();
}


namespace {

/// A helper class to collect information about types
/// used by a SILModule, SILInstruction or other types.
class UsedTypesCollector {
  llvm::DenseSet<CanType> UsedTypes;
  llvm::DenseSet<CanType> UsedMetatypes;
public:
  void collect(CanType Ty);
  void collectMetatypes(CanType Ty);
  void collect(const SILWitnessTable &WT);
  void collect(const SILInstruction &I);
  void collectMetatypes(const SILInstruction &I);
  void collect(const SILFunction &F);
  void collect(SILModule &I);

  const llvm::DenseSet<CanType> &getTypes() const {
    return UsedTypes;
  }

  const llvm::DenseSet<CanType> &getMetatypes() const {
    return UsedTypes;
  }
};

void UsedTypesCollector::collect(CanType Ty) {
  // If it is a metatype, drill down until we find
  // the actual type.
  while(auto MT = dyn_cast<AnyMetatypeType>(Ty)) {
    Ty = MT->getInstanceType()->getCanonicalType();
    //llvm::dbgs() << "Got the instance type: " << Ty << "\n";
  }

  // Bail if the type was processed already.
  if (!UsedTypes.insert(Ty).second)
    return;

  DEBUG(llvm::dbgs() << "Found type: " << Ty << "\n");

  auto NTD = Ty->getAnyNominal();
  // Generic signature of the type, if present.
  GenericSignature *Signature = nullptr;

  if (NTD) {
    // Add referenced protocols.
    auto Protocols = NTD->getAllProtocols();
    for (auto P : Protocols) {
     llvm::dbgs() << "Adding protocol of " << NTD->getName() << ": "
                     << P->getNameStr() << "\n";
     collect(P->getDeclaredInterfaceType()->getCanonicalType());
    }
#if 0
    for (auto C : NTD->getAllConformances()) {
      if (!M.lookUpWitnessTable(C)) {

      }
    }
#endif

    // Add referenced superclass.
    if (auto CD = Ty->getClassOrBoundGenericClass()) {
      auto Superclass = CD->getSuperclass();
      if (Superclass) {
        llvm::dbgs() << "Adding superclass of " << CD->getName() << ": "
                     << Superclass->getAnyNominal()->getNameStr() << "\n";
        collect(Superclass->getCanonicalType());
      }
    }

    auto GTD = NTD->getAsNominalTypeOrNominalTypeExtensionContext();
    if (!GTD)
      return;

    // Add types used as generic arguments.
    if (auto BGT = dyn_cast<BoundGenericType>(Ty)) {
      for (auto GA : BGT->getGenericArgs()) {
        collect(GA->getCanonicalType());
      }
    }

    Signature = GTD->getGenericSignature();
  }

  auto FnTy = dyn_cast<SILFunctionType>(Ty);

  if (!FnTy && !NTD) {
    return;
  }

  if (FnTy) {
    // Add any types referenced by the function type.
    // E.g. it could detect protocols used in requirements.
    Ty.visit([this, &Ty](Type ty) {
      if (ty->getCanonicalType() == Ty)
        return;
      if (UsedTypes.count(ty->getCanonicalType()))
        return;
      collect(ty->getCanonicalType());
    });

    if (FnTy->isPolymorphic())
      Signature = FnTy->getGenericSignature();
  }

  if (!Signature)
    return;

  // Add types referenced in requirements.
  auto Requirements = Signature->getRequirements();
  for (auto Req : Requirements) {
    switch (Req.getKind()) {
    case RequirementKind::Layout: {
      auto FirstTy = Req.getFirstType();
      auto FirstNTD = FirstTy->getAnyNominal();
      collect(FirstTy->getCanonicalType());
      break;
    }
    default:
      auto FirstTy = Req.getFirstType();
      auto SecondTy = Req.getSecondType();
      auto FirstNTD = FirstTy->getAnyNominal();
      auto SecondNTD = SecondTy->getAnyNominal();
      //if (FirstNTD) {
        collect(FirstTy->getCanonicalType());
#if 0
        auto Result = UsedTypes.insert(
            FirstNTD->getDeclaredType()->getCanonicalType());
        if (Result.second) {
          llvm::dbgs() << "Found a new type in function type: "
                       << FirstNTD->getNameStr() << "\n";
        }
#endif
      //}
      //if (SecondNTD) {
        collect(SecondTy->getCanonicalType());
#if 0
        auto Result = UsedTypes.insert(
            SecondNTD->getDeclaredType()->getCanonicalType());
        if (Result.second) {
          llvm::dbgs() << "Found a new type in function type: "
                       << SecondNTD->getNameStr() << "\n";
        }
#endif
      //}
      break;
    }
  }
}

void UsedTypesCollector::collectMetatypes(CanType Ty) {
  // If it is a metatype, drill down until we find
  // the actual type.
  while(auto MT = dyn_cast<AnyMetatypeType>(Ty)) {
    Ty = MT->getInstanceType()->getCanonicalType();
    //llvm::dbgs() << "Got the instance type: " << Ty << "\n";
  }

  // Bail if the type was processed already.
  if (!UsedMetatypes.insert(Ty).second)
    return;

  DEBUG(llvm::dbgs() << "collectMetatypes: Found type: " << Ty << "\n");

  auto NTD = Ty->getAnyNominal();

  if (NTD) {
    auto GTD = NTD->getAsNominalTypeOrNominalTypeExtensionContext();
    if (!GTD)
      return;

    // Add types used as generic arguments.
    if (auto BGT = dyn_cast<BoundGenericType>(Ty)) {
      for (auto GA : BGT->getGenericArgs()) {
        collectMetatypes(GA->getCanonicalType());
      }
    }
  }
}


void UsedTypesCollector::collect(const SILWitnessTable &WT) {
  for (auto Witness : WT.getEntries()) {
    switch (Witness.getKind()) {
    case swift::SILWitnessTable::Invalid:
      continue;
    case swift::SILWitnessTable::Method: {
      // method #declref: @function
      auto &methodWitness = Witness.getMethodWitness();
      break;
    }
    case swift::SILWitnessTable::AssociatedType: {
      // associated_type AssociatedTypeName: ConformingType
      auto &assocWitness = Witness.getAssociatedTypeWitness();
      collect(assocWitness.Witness);
      break;
    }
    case swift::SILWitnessTable::AssociatedTypeProtocol: {
      auto &assocProtoWitness = Witness.getAssociatedTypeProtocolWitness();
      if (assocProtoWitness.Witness.isConcrete())
        collect(assocProtoWitness.Witness.getConcrete()
                             ->getType()
                             ->getCanonicalType());
      break;
    }
    case swift::SILWitnessTable::BaseProtocol: {
      auto &baseProtoWitness = Witness.getBaseProtocolWitness();
      collect(
          baseProtoWitness.Witness->getType()->getCanonicalType());
      break;
    }
    case swift::SILWitnessTable::MissingOptional: {
      break;
    }
    }
  }
}

/// Collect all types used by a SIL instruction.
/// TODO: Figure out which conformances may be used by the instruction.
void UsedTypesCollector::collect(const SILInstruction &I) {
  SmallVector<CanType, 8> InstUsedTypes;
  // Add types of type operands.
  if (I.collectTypeOperands(InstUsedTypes)) {
    if (!InstUsedTypes.empty()) {
      DEBUG(llvm::dbgs() << "Adding types from instruction: "; I.dump());
      for (auto Ty : InstUsedTypes)
        collect(Ty);
    }
  }
  // Add types of all operands.
  for (auto &Op : I.getAllOperands()) {
    collect(Op.get()->getType().getSwiftRValueType());
  }
  // Add type of the result.
  if (I.hasValue())
    collect(I.getType().getSwiftRValueType());

  collectMetatypes(I);
}

void UsedTypesCollector::collectMetatypes(const SILInstruction &I) {
  SmallVector<CanType, 8> InstUsedTypes;
  // Add types of type operands.
  I.collectTypeOperands(InstUsedTypes);

  if (ApplySite AI = ApplySite::isa(const_cast<SILInstruction *>(&I))) {
    if (!AI.hasSubstitutions())
      return;
    // Analyze generic applies.
    auto Subs = AI.getSubstitutions();
    // Mark that each type passed as generic parameter needs type
    // metadata to be emitted.
    for (auto Sub : Subs) {
      collectMetatypes(Sub.getReplacement()->getCanonicalType());
    }
    return;
  }

  // Metatype instructions refer to a metatype explicitly.
  if (isa<MetatypeInst>(&I) ||
      isa<ValueMetatypeInst>(&I) ||
      isa<ExistentialMetatypeInst>(&I)) {
    collectMetatypes(I.getType().getSwiftRValueType());
    return;
  }

  // Target type of conversion instructions could need a
  // metatype.
  if (auto CI = dyn_cast<ConversionInst>(&I)) {
    collectMetatypes(I.getType().getSwiftRValueType());
    return;
  }

  if (isa<CheckedCastBranchInst>(&I) ||
      isa<CheckedCastAddrBranchInst>(&I)) {
    for (auto T : InstUsedTypes) {
      collectMetatypes(T);
    }
    return;
  }

  // existentials may need metatypes.
  if (isa<InitExistentialAddrInst>(&I) ||
      isa<InitExistentialRefInst>(&I) ||
      isa<InitExistentialMetatypeInst>(&I)) {
    for (auto T : InstUsedTypes) {
      collectMetatypes(T);
    }
    return;
  }
}


void UsedTypesCollector::collect(const SILFunction &Fn) {

  collect(Fn.getLoweredFunctionType());
  for (auto &BB : Fn) {
    // Add types of all BB arguments.
    for (auto &BBArg : BB.getArguments()) {
      collect(BBArg->getType().getSwiftRValueType());
    }

    for (auto &I : BB) {
      collect(I);
    }
  }
}

void UsedTypesCollector::collect(SILModule &M) {
  for (auto &Fn : M) {
    DEBUG(llvm::dbgs() << "Collecting types used by SIL function "
                       << Fn.getName() << "\n");
    collect(Fn);
  }
}

/// Swift runtime library refers to a number of SIL functions.
/// All of those functions are usually marked with @_silgen_name.
/// Force linking of all those functions, because they may be
/// invoked by the runtime.

/// FIXME: Use a whitelist for now. Use some kind of automation
/// to keep it always in sync with the standrad library.
/// TODO: Write a test, which has an empty input swift file.
/// Compiling this test should still result in a an SIL file
/// that contains definitions for all SIL functions from the
/// whitelist.
static const char *StdlibRuntimeFunctions[] = {
#if 0
  "xyz",
#else
  // @_silgen_name annotated functions
  "swift_stringFromUTF8InRawMemory",
  "swift_stdlib_getErrorUserInfoNSDictionary",
  "swift_stdlib_getErrorEmbeddedNSErrorIndirect",
  "swift_stdlib_getErrorDomainNSString",
  "swift_stdlib_getErrorCode",
  "swift_stdlib_Hashable_isEqual_indirect",
  "swift_stdlib_Hashable_hashValue_indirect",
  "_swift_stdlib_makeAnyHashableUsingDefaultRepresentation",
  "_swift_setDownCastIndirect",
  "_swift_setDownCastConditionalIndirect",
  "_swift_dictionaryDownCastIndirect",
  "_swift_dictionaryDownCastConditionalIndirect",
  "_swift_convertToAnyHashableIndirect",
  "_swift_bridgeNonVerbatimFromObjectiveCToAny",
  "_swift_bridgeNonVerbatimBoxedValue",
  "_swift_arrayDownCastIndirect",
  "_swift_arrayDownCastConditionalIndirect",
  "_swift_anyHashableDownCastConditionalIndirect",
  //"swift_getSummary",
  // Mirrors
  //"_TFVs11_ObjCMirrorg7summarySS",
  //"_TFVs12_ClassMirrorg7summarySS",
  //"_TFVs12_TupleMirrorg7summarySS",
  //"_TFVs13_StructMirrorg7summarySS",
  //"_TFVs11_EnumMirrorg7summarySS",
  //"_TTWVs13_OpaqueMirrors7_MirrorsFS0_g7summarySS",
  //"_TTWVs15_MetatypeMirrors7_MirrorsFS0_g7summarySS",
  // BridgableMetatype
  "_TTWVs19_BridgeableMetatypes21_ObjectiveCBridgeablesFS0_19_bridgeToObjectiveCfT_wx15_ObjectiveCType",
#endif
};

static void linkFunctionsRequiredByRuntime(SILModule &M) {
  ArrayRef<const char *> ExposedStdlibRuntimeFunctions(StdlibRuntimeFunctions);
  for (auto F : ExposedStdlibRuntimeFunctions) {
    SILFunction *Fn;
    Fn = M.lookUpFunction(F);
    if (!Fn) {
      M.linkFunction(F, SILModule::LinkingMode::LinkAll);
      //M.linkFunction(F, SILModule::LinkingMode::LinkNormal);
      DEBUG(llvm::dbgs() << "Trying to link a @_silgen_name function: " << F
                         << "\n");
      Fn = M.lookUpFunction(F);
      if (!Fn)
        continue;
    }
    // Mark it as non-removable, because runtime may invoke it.
    Fn->setKeepAsPublic(true);
  }
}

/// Link all functions and types (i.e. vtables and witness tables)
/// used by the SIL module.
///
/// This works by first linking the entry points required by the
/// runtime library and then recursively linking anything required
/// by the current module. Every time a new function, vtable or
/// witness table is linked, it may result in loading its entries
/// which may require loading further functions, vtables and 
/// witness tables. The process is finished when a fixed point
/// is reached, i.e. no new entities that need to be linked are
/// found.
void linkAllUsedFunctionsAndTypes(SILModule &M) {
  auto &ASTTypes = M.getDeserializedNominalTypesSet();
  UsedTypesCollector UsedTypes;

  // Set of types that were processed already.
  llvm::DenseSet<CanType> ProcessedTypes;

  // M.linkAllWitnessTables();
  // M.linkAllVTables();

  // Link all Swift methods which are potentially used by the
  // runtime library.
  // TODO: This can be improved and made more precise:
  // - Create an analysis to figure out which runtime calls
  // are used in the user program.
  // - Have a mapping from a runtime call name to a set of
  // Swift methods that are possibly invoked by such a call.
  // - Link only those Swift methods which can be really called.
  linkFunctionsRequiredByRuntime(M);

  // Iterate until no new types can be found.
  while (true) {

    SmallVector<CanType, 64> Types(UsedTypes.getTypes().begin(), UsedTypes.getTypes().end());
    // Prepare UsedType for accumulating new types for the next iteration.
    // UsedTypes.clear();
    bool Updated = false;
    // FIXME: lookup may modify the set?
    for (auto DNT : Types) {
      // Nothing to do, if the type was processed already.
      if (!ProcessedTypes.insert(DNT).second)
        continue;

      Updated = true;

      DEBUG(llvm::dbgs() << "linkASTTypes: Processing type: " << DNT << "\n");
      if (auto NTD = DNT->getNominalOrBoundGenericNominal()) {
        // Try to link the witness tables for this type.
        // Be very naive at the moment: Load witness tables for all
        // protocols implemented by the type.
        auto Conformances = NTD->getAllConformances();
        if (!Conformances.empty()) {
          DEBUG(llvm::dbgs() << "Processing conformances for " << DNT << "\n");
        } else {
          auto Protocols = NTD->getAllProtocols();
          for (auto P : Protocols) {
            DEBUG(llvm::dbgs() << "Processing protocol of " << NTD->getName()
                               << ": " << P->getNameStr() << "\n");
          }
        }

        for (auto C : Conformances) {
          auto WT = M.lookUpWitnessTable(C);
          // Do not eagrly load all witness tables!
          //continue;
          if (!WT) {
            WT = M.createWitnessTableDeclaration(C, SILLinkage::Public);
            WT = M.lookUpWitnessTable(C);
            if (!WT) {
              DEBUG(llvm::dbgs()
                        << "Could not create and load SIL witness table "
                        << WT->getName() << "\n"
                        << "for conformance ";
                    C->dump());
            }
            if (WT) {
              llvm::dbgs() << "Loaded SIL witness table " << WT->getName() << "\n";
              WT->dump();
              for (auto Witness : WT->getEntries()) {
                switch (Witness.getKind()) {
                case swift::SILWitnessTable::Invalid:
                  continue;
                case swift::SILWitnessTable::Method: {
                  // method #declref: @function
                  auto &methodWitness = Witness.getMethodWitness();
                  break;
                }
                case swift::SILWitnessTable::AssociatedType: {
                  // associated_type AssociatedTypeName: ConformingType
                  auto &assocWitness = Witness.getAssociatedTypeWitness();
                  UsedTypes.collect(assocWitness.Witness);
                  break;
                }
                case swift::SILWitnessTable::AssociatedTypeProtocol: {
                  auto &assocProtoWitness =
                      Witness.getAssociatedTypeProtocolWitness();
                  if (assocProtoWitness.Witness.isConcrete())
                    UsedTypes.collect(assocProtoWitness.Witness.getConcrete()
                                ->getType()
                                ->getCanonicalType());
                  break;
                }
                case swift::SILWitnessTable::BaseProtocol: {
                  auto &baseProtoWitness = Witness.getBaseProtocolWitness();
                  UsedTypes.collect(
                      baseProtoWitness.Witness->getType()->getCanonicalType());
                  break;
                }
                case swift::SILWitnessTable::MissingOptional: {
                  break;
                }
                }
              }
            }
          } else {
            DEBUG(llvm::dbgs() << "Witness table is loaded already: "
                               << WT->getName() << "\n";
                  WT->dump());
          }
        }

        // No need to do anything if the type was processed already.
        if (!ASTTypes.insert(NTD).second)
          continue;
        DEBUG(llvm::dbgs() << "Linking nominal type: " << NTD->getNameStr()
                           << "\n");
      }

      if (auto CD = DNT->getClassOrBoundGenericClass()) {
        // Load a vtable for each deserialized class.
        M.lookUpVTable(CD);
        // Load some special members which are not loaded
        // by default if they are not referenced.
        for (auto Member : CD->getMembers()) {
          auto FD = dyn_cast<AbstractFunctionDecl>(Member);
          if (!FD)
            continue;
          // if (!FD->isObjC())
          //  continue;
          // Force loading of the SIL function for this ObjC member.
          SILDeclRef::Loc MemberLoc = FD;
          auto Kind = SILDeclRef::Kind::Func;
          if (isa<ConstructorDecl>(FD)) {
            Kind = SILDeclRef::Kind::Initializer;
          } else if (isa<DestructorDecl>(FD)) {
            Kind = SILDeclRef::Kind::Deallocator;
          }

          // The functions we are interested in are @objc functions
          // and destructors.
          if (Kind != SILDeclRef::Kind::Deallocator && !FD->isObjC())
            continue;
          // Only load constructors and destructors.
          // if (Kind == SILDeclRef::Kind::Func)
          //  continue;
          if (Kind != SILDeclRef::Kind::Func) {
            SILDeclRef MemberRef(FD, Kind, ResilienceExpansion::Minimal,
                                 SILDeclRef::ConstructAtNaturalUncurryLevel,
                                 /* isForeign */ true);
            auto MangledNameStr = MemberRef.mangle();
            StringRef MangledName = MangledNameStr;
            if (M.lookUpFunction(MangledName))
              continue;
            llvm::dbgs() << "Linking class member: " << MangledName
                               << "\n";
            DEBUG(llvm::dbgs() << "Linking class member: " << MangledName
                               << "\n");
            if (!M.hasFunction(MangledName, SILLinkage::Private))
              M.linkFunction(MemberRef, SILModule::LinkingMode::LinkNormal);
          } else {
            SILDeclRef MemberRef(MemberLoc, ResilienceExpansion::Minimal,
                                 SILDeclRef::ConstructAtNaturalUncurryLevel,
                                 /* isForeign */ true);
            auto MangledNameStr = MemberRef.mangle();
            StringRef MangledName = MangledNameStr;
            DEBUG(llvm::dbgs() << "Linking class member: " << MangledName
                               << "\n");
            // assert(false);
            if (!M.hasFunction(MangledName, SILLinkage::Private))
              M.linkFunction(MemberRef, SILModule::LinkingMode::LinkNormal);
          }
        }
      }
    }
    // Re-scan functions.
    // In principle, we only need to scan the newly loaded functions.
    if (!Updated && !UsedTypes.getTypes().empty())
      break;

    UsedTypes.collect(M);
  }

  for (auto MT : UsedTypes.getMetatypes()) {
    llvm::dbgs() << "Metatype may be needed: " << MT << "\n";
  }
}

/// Copies code from the standard library into the user program to enable
/// optimizations.
class SILLinker : public SILModuleTransform {
  bool IsStatic;
public:
  SILLinker(bool IsStatic = false) : IsStatic(IsStatic) {
  }

  void run() override {
    SILModule &M = *getModule();

    if (IsStatic && M.isWholeProgram()) {
      // Link all methods and types.
      linkAllUsedFunctionsAndTypes(M);
    }

    for (auto &Fn : M)
      if (M.linkFunction(&Fn, SILModule::LinkingMode::LinkAll))
          invalidateAnalysis(&Fn, SILAnalysis::InvalidationKind::Everything);
  }

  StringRef getName() override { return "SIL Linker"; }
};
} // end anonymous namespace


SILTransform *swift::createSILLinker() {
  //return new SILLinker();
  return new SILLinker(/* IsStatic */ true);
}

SILTransform *swift::createStaticSILLinker() {
  return new SILLinker(/* IsStatic */ true);
}
