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
static void collectAllUsedTypes(SILInstruction &I,
                                llvm::DenseSet<CanType> &UsedTypes) {
  SmallVector<CanType, 8> InstUsedTypes;
  // Add types of type operands.
  if (I.collectTypeOperands(InstUsedTypes)) {
    for (auto Ty : InstUsedTypes)
      UsedTypes.insert(Ty);
  }
  // Add types of all operands.
  for (auto &Op : I.getAllOperands()) {
    UsedTypes.insert(Op.get()->getType().getSwiftRValueType());
  }
  // Add type of the result.
  if (I.hasValue())
    UsedTypes.insert(I.getType().getSwiftRValueType());
}

static void collectAllUsedTypes(SILFunction &Fn,
                                llvm::DenseSet<CanType> &UsedTypes) {
  for (auto &BB : Fn) {
    // Add types of all BB arguments.
    for (auto &BBArg : BB.getBBArgs()) {
      UsedTypes.insert(BBArg->getType().getSwiftRValueType());
    }

    for (auto &I : BB) {
      collectAllUsedTypes(I, UsedTypes);
    }
  }
}

static void collectAllUsedTypes(SILModule &M,
                                llvm::DenseSet<CanType> &UsedTypes) {
  for (auto &Fn : M) {
    collectAllUsedTypes(Fn, UsedTypes);
  }
}

static void linkASTTypes(SILModule &M, llvm::DenseSet<CanType> &UsedTypes) {
#if 1
    // FIXME: lookup may modify the set?
    //for (auto DNT : M.getDeserializedNominalTypes()) {
    for (auto DNT : UsedTypes) {
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

          if (Kind != SILDeclRef::Kind::Deallocator && !FD->isObjC())
            continue;
          if (Kind != SILDeclRef::Kind::Func) {
            SILDeclRef MemberRef(FD, Kind, ResilienceExpansion::Minimal,
                                 SILDeclRef::ConstructAtNaturalUncurryLevel,
                                 /* isForeign */ true);
            auto MangledNameStr = MemberRef.mangle();
            StringRef MangledName = MangledNameStr;
            if (!M.hasFunction(MangledName, SILLinkage::Private))
              M.linkFunction(MemberRef,
                                  SILModule::LinkingMode::LinkNormal);
          } else {
            SILDeclRef MemberRef(MemberLoc, ResilienceExpansion::Minimal,
                                 SILDeclRef::ConstructAtNaturalUncurryLevel,
                                 /* isForeign */ true);
            auto MangledNameStr = MemberRef.mangle();
            StringRef MangledName = MangledNameStr;
            if (!M.hasFunction(MangledName, SILLinkage::Private))
              M.linkFunction(MemberRef,
                                  SILModule::LinkingMode::LinkNormal);
          }
        }
      }
    }
#endif

}

/// Copies code from the standard library into the user program to enable
/// optimizations.
class SILLinker : public SILModuleTransform {

  void run() override {
    SILModule &M = *getModule();

    if (M.getOptions().Optimization ==
        SILOptions::SILOptMode::OptimizeWholeProgram) {
      // Collect all AST types used by SIL.
      llvm::DenseSet<CanType> UsedTypes;
      collectAllUsedTypes(M, UsedTypes);
      // Link all methods required by those types.
      linkASTTypes(M, UsedTypes);
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
