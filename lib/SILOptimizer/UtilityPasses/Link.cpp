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

static void collectUsedTypes(CanType Ty, llvm::DenseSet<CanType> &UsedTypes) {
  // If it is a metatype, drill down until we find
  // the actual type.
  while(auto MT = dyn_cast<AnyMetatypeType>(Ty)) {
    Ty = MT->getInstanceType()->getCanonicalType();
    //llvm::dbgs() << "Got the instance type: " << Ty << "\n";
  }

  // Bail if the type was processed already.
  if (!UsedTypes.insert(Ty).second)
    return;

  llvm::dbgs() << "Linked type: " << Ty << "\n";

  auto NTD = Ty->getAnyNominal();
  // Generic signature of the type, if present.
  GenericSignature *Signature = nullptr;

  if (NTD) {
    // Add referenced protocols.
    auto Protocols = NTD->getAllProtocols();
    for (auto P : Protocols) {
     llvm::dbgs() << "Adding protocol of " << NTD->getName() << ": "
                     << P->getNameStr() << "\n";
     collectUsedTypes(P->getDeclaredInterfaceType()->getCanonicalType(),
                       UsedTypes);
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
        collectUsedTypes(Superclass->getCanonicalType(), UsedTypes);
      }
    }

    auto GTD = NTD->getAsNominalTypeOrNominalTypeExtensionContext();
    if (!GTD)
      return;

    // Add types used as generic arguments.
    if (auto BGT = dyn_cast<BoundGenericType>(Ty)) {
      for (auto GA : BGT->getGenericArgs()) {
        collectUsedTypes(GA->getCanonicalType(), UsedTypes);
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
    Ty.visit([&UsedTypes, &Ty](Type ty) {
      if (ty->getCanonicalType() == Ty)
        return;
      if (UsedTypes.count(ty->getCanonicalType()))
        return;
      collectUsedTypes(ty->getCanonicalType(), UsedTypes);
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
      collectUsedTypes(FirstTy->getCanonicalType(), UsedTypes);
      break;
    }
    default:
      auto FirstTy = Req.getFirstType();
      auto SecondTy = Req.getSecondType();
      auto FirstNTD = FirstTy->getAnyNominal();
      auto SecondNTD = SecondTy->getAnyNominal();
      //if (FirstNTD) {
        collectUsedTypes(FirstTy->getCanonicalType(), UsedTypes);
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
        collectUsedTypes(SecondTy->getCanonicalType(), UsedTypes);
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

static void collectAllUsedTypes(SILInstruction &I,
                                llvm::DenseSet<CanType> &UsedTypes) {
  SmallVector<CanType, 8> InstUsedTypes;
  // Add types of type operands.
  if (I.collectTypeOperands(InstUsedTypes)) {
    if (!InstUsedTypes.empty()) {
      llvm::dbgs() << "Adding types from instruction: ";
      I.dump();
      for (auto Ty : InstUsedTypes)
        collectUsedTypes(Ty, UsedTypes);
    }
  }
  // Add types of all operands.
  for (auto &Op : I.getAllOperands()) {
    collectUsedTypes(Op.get()->getType().getSwiftRValueType(), UsedTypes);
  }
  // Add type of the result.
  if (I.hasValue())
    collectUsedTypes(I.getType().getSwiftRValueType(), UsedTypes);
}

static void collectAllUsedTypes(SILFunction &Fn,
                                llvm::DenseSet<CanType> &UsedTypes) {
  for (auto &BB : Fn) {
    // Add types of all BB arguments.
    for (auto &BBArg : BB.getArguments()) {
      collectUsedTypes(BBArg->getType().getSwiftRValueType(), UsedTypes);
    }

    for (auto &I : BB) {
      collectAllUsedTypes(I, UsedTypes);
    }
  }
}

static void collectAllUsedTypes(SILModule &M,
                                llvm::DenseSet<CanType> &UsedTypes) {
  for (auto &Fn : M) {
    llvm::dbgs() << "Collecting types used by SIL function " << Fn.getName() << "\n";
    collectAllUsedTypes(Fn, UsedTypes);
  }
}

static void linkASTTypes(SILModule &M, llvm::DenseSet<CanType> &UsedTypes) {
    auto &ASTTypes = M.getDeserializedNominalTypesSet();
    //ASTTypes.clear();

    // Iterate until no new types can be found.
    while (!UsedTypes.empty()) {

    SmallVector<CanType, 64> Types(UsedTypes.begin(), UsedTypes.end());
    // Prepare UsedType for accumulating new types for the next iteration.
    UsedTypes.clear();

#if 1
    // FIXME: lookup may modify the set?
    //for (auto DNT : M.getDeserializedNominalTypes()) {
    for (auto DNT : Types) {
      llvm::dbgs() << "linkASTTypes: Processing type: " << DNT << "\n";
      if (auto NTD = DNT->getNominalOrBoundGenericNominal()) {
        // Try to link the witness tables for this type.
        // Be very naive at the moment: Load witness tables for all
        // protocols implemented by the type.
        auto Conformances = NTD->getAllConformances();
        if (!Conformances.empty()) {
          llvm::dbgs() << "Processing conformances for " << DNT << "\n";
        } else {
          auto Protocols = NTD->getAllProtocols();
          for (auto P : Protocols) {
            llvm::dbgs() << "Processing protocol of " << NTD->getName() << ": "
                         << P->getNameStr() << "\n";
          }
        }

        for (auto C : Conformances) {
          auto WT = M.lookUpWitnessTable(C);
          if (!WT) {
            M.createWitnessTableDeclaration(C, SILLinkage::Public);
            WT = M.lookUpWitnessTable(C);
            if (!WT) {
              llvm::dbgs() << "Could not create and load SIL witness table "
                           << WT->getName() << "\n"
                           << "for conformance "; 
              C->dump();
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
                  collectUsedTypes(assocWitness.Witness, UsedTypes);
                  break;
                }
                case swift::SILWitnessTable::AssociatedTypeProtocol: {
                  auto &assocProtoWitness =
                      Witness.getAssociatedTypeProtocolWitness();
                  if (assocProtoWitness.Witness.isConcrete())
                    collectUsedTypes(assocProtoWitness.Witness.getConcrete()
                                         ->getType()
                                         ->getCanonicalType(),
                                     UsedTypes);
                  break;
                }
                case swift::SILWitnessTable::BaseProtocol: {
                  auto &baseProtoWitness = Witness.getBaseProtocolWitness();
                  collectUsedTypes(
                      baseProtoWitness.Witness->getType()->getCanonicalType(),
                      UsedTypes);
                  break;
                }
                case swift::SILWitnessTable::MissingOptional: {
                  break;
                }
                }
              }
            }
          } else {
            llvm::dbgs() << "Witness table is loaded already: " << WT->getName() << "\n";
            WT->dump();
          }
        }

        if (ASTTypes.count(NTD))
          continue;
        ASTTypes.insert(NTD);
        llvm::dbgs() << "Linking nominal type: " << NTD->getNameStr() << "\n";

#if 0
        auto GTD = NTD->getAsGenericTypeOrGenericTypeExtensionContext();
        if (GTD) {
          GTD->getConfo
          auto Signature = GTD->getGenericSignature();
          auto Requirements = Signature->getRequirements();
          for (auto Req : Requirements) {
            if (Req.getKind() != RequirementKind::Conformance)
              continue;
            Req.getSecondType();
          }
        }
#endif
      }

      //if (auto CD = dyn_cast<ClassDecl>(DNT)) {
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
          //if (Kind == SILDeclRef::Kind::Func)
          //  continue;
          if (Kind != SILDeclRef::Kind::Func) {
            SILDeclRef MemberRef(FD, Kind, ResilienceExpansion::Minimal,
                                 SILDeclRef::ConstructAtNaturalUncurryLevel,
                                 /* isForeign */ true);
            auto MangledNameStr = MemberRef.mangle();
            StringRef MangledName = MangledNameStr;
            if (M.lookUpFunction(MangledName))
              continue;
            llvm::dbgs() << "Linking class member: " << MangledName << "\n";
            if (!M.hasFunction(MangledName, SILLinkage::Private))
              M.linkFunction(MemberRef,
                                  SILModule::LinkingMode::LinkNormal);
          } else {
            SILDeclRef MemberRef(MemberLoc, ResilienceExpansion::Minimal,
                                 SILDeclRef::ConstructAtNaturalUncurryLevel,
                                 /* isForeign */ true);
            auto MangledNameStr = MemberRef.mangle();
            StringRef MangledName = MangledNameStr;
            llvm::dbgs() << "Linking class member: " << MangledName << "\n";
            //assert(false);
            if (!M.hasFunction(MangledName, SILLinkage::Private))
              M.linkFunction(MemberRef,
                                  SILModule::LinkingMode::LinkNormal);
          }
        }
      }
    }
#endif
    }
}

/// Swift runtime library refers to a number of SIL functions.
/// All of those functions are usually marked with @_silgen_name.
/// Force linking of all those functions, because they may be
/// invoked by the runtime.

/// FIXME: Use a whitelist for now. Use some kind of automation
/// to keep it always in sync with the standrad library.
static const char *StdlibRuntimeFunctions[] = {
  // @_silgen_name annotated functions
  "swift_stringFromUTF8InRawMemory",
  "swift_stdlib_getErrorUserInfoNSDictionary",
  "swift_stdlib_getErrorEmbeddedNSErrorIndirect",
  "swift_stdlib_getErrorDomainNSString",
  "swift_stdlib_getErrorCode",
  "swift_stdlib_Hashable_isEqual_indirect",
  "swift_stdlib_Hashable_hashValue_indirect",
  "swift_getSummary",
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
  // Mirrors
  "_TFVs11_ObjCMirrorg7summarySS",
  "_TFVs12_ClassMirrorg7summarySS",
  "_TFVs12_TupleMirrorg7summarySS",
  "_TFVs13_StructMirrorg7summarySS",
  "_TFVs11_EnumMirrorg7summarySS",
  "_TTWVs13_OpaqueMirrors7_MirrorsFS0_g7summarySS",
  "_TTWVs15_MetatypeMirrors7_MirrorsFS0_g7summarySS",
  // BridgableMetatype
  "_TTWVs19_BridgeableMetatypes21_ObjectiveCBridgeablesFS0_19_bridgeToObjectiveCfT_wx15_ObjectiveCType",
};

static void linkFunctionsRequiredByRuntime(SILModule &M,
                                           llvm::DenseSet<CanType> &UsedTypes) {
  ArrayRef<const char *> ExposedStdlibRuntimeFunctions(StdlibRuntimeFunctions);
  for (auto F : ExposedStdlibRuntimeFunctions) {
    SILFunction *Fn;
    Fn = M.lookUpFunction(F);
    if (!Fn) {
      M.linkFunction(F, SILModule::LinkingMode::LinkAll);
      //M.linkFunction(F, SILModule::LinkingMode::LinkNormal);
      llvm::dbgs() << "Trying to link a @_silgen_name function: " << F << "\n";
      Fn = M.lookUpFunction(F);
      if (!Fn)
        continue;
    }
    // Mark it as non-removable, because runtime may invoke it.
    Fn->setKeepAsPublic(true);
    // Add any types referenced by the function type.
    // E.g. it could detect protocols used in requirements.
    collectUsedTypes(Fn->getLoweredFunctionType(), UsedTypes);
    // TODO: Any witness tables referenced from the non-removabe functions
    // need to be loaded.
  }
}

/// Copies code from the standard library into the user program to enable
/// optimizations.
class SILLinker : public SILModuleTransform {

  void run() override {
    SILModule &M = *getModule();

    if (M.isWholeProgram()) {
      //M.linkAllWitnessTables();
      //M.linkAllVTables();
      // Link all methods used by runtime.
      llvm::DenseSet<CanType> UsedTypes;
      linkFunctionsRequiredByRuntime(M, UsedTypes);
      // FIXME: loading all witness tables is not such a great idea.
      // It loads a lot of tables containing objc methods. Such entries
      // cannot be removed, even if they are not invoked by the program,
      // because they could be called by ObjC runtime.
      // TODO: Load a whitelisted set of witness tables by witness tables names?
      // Or may be we should have a whitelist of conformances?
      // E.g. if we have T : P, then we lookup type T, protocol P, create a conformance,
      // create a declaratin of a WitnessTable using this information.
      // M.linkAllWitnessTables();
      // Collect all AST types used by SIL.
      collectAllUsedTypes(M, UsedTypes);
      // Link all methods required by those types.
      linkASTTypes(M, UsedTypes);
#if 0
      // Collect all AST types used by SIL.
      collectAllUsedTypes(M, UsedTypes);
      // Link all methods required by those types.
      linkASTTypes(M, UsedTypes);
#endif
    }
    for (auto &Fn : M)
      if (M.linkFunction(&Fn, SILModule::LinkingMode::LinkAll))
          invalidateAnalysis(&Fn, SILAnalysis::InvalidationKind::Everything);
  }

  StringRef getName() override { return "SIL Linker"; }
};
} // end anonymous namespace


SILTransform *swift::createSILLinker() {
  return new SILLinker();
}
