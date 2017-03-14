//===--- ClosureSpecializer.cpp - Performs Closure Specialization ---------===//
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
///
/// \file
///
/// Closure Specialization
/// ----------------------
///
/// The purpose of the algorithm in this file is to perform the following
/// transformation: given a closure passed into a function which the closure is
/// then invoked in, clone the function and create a copy of the closure inside
/// the function. This closure will be able to be eliminated easily and the
/// overhead is gone. We then try to remove the original closure.
///
/// There are some complications. They are listed below and how we work around
/// them:
///
/// 1. If we support the specialization of closures with multiple user callsites
///    that can be specialized, we need to ensure that any captured values have
///    their reference counts adjusted properly. This implies for every
///    specialized call site, we insert an additional retain for each captured
///    argument with reference semantics. We will pass them in as extra @owned
///    to the specialized function. This @owned will be consumed by the "copy"
///    partial apply that is in the specialized function. Now the partial apply
///    will own those ref counts. This is unapplicable to thin_to_thick_function
///    since they do not have any captured args.
///
/// 2. If the closure was passed in @owned vs if the closure was passed in
///    @guaranteed. If the original closure was passed in @owned, then we know
///    that there is a balancing release for the new "copy" partial apply. But
///    since the original partial apply no longer will have that corresponding
///    -1, we need to insert a release for the old partial apply. We do this
///    right after the old call site where the original partial apply was
///    called. This ensures we do not shrink the lifetime of the old partial
///    apply. In the case where the old partial_apply was passed in at +0, we
///    know that the old partial_apply does not need to have any ref count
///    adjustments. On the other hand, the new "copy" partial apply in the
///    specialized function now needs to be balanced lest we leak. Thus we
///    insert a release right before any exit from the function. This ensures
///    that the release occurs in the epilog after any retains associated with
///    @owned return values.
///
/// 3. Handling addresses. We currently do not handle address types. We can in
///    the future by introducing alloc_stacks.
///
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "closure-specialization"
#include "swift/AST/GenericSignatureBuilder.h"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SILOptimizer/Utils/SpecializationMangler.h"
#include "swift/SIL/Mangle.h"
#include "swift/SIL/SILCloner.h"
#include "swift/SIL/SILFunction.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SIL/SILModule.h"
#include "swift/SILOptimizer/Analysis/BasicCalleeAnalysis.h"
#include "swift/SILOptimizer/Analysis/CFG.h"
#include "swift/SILOptimizer/Analysis/FunctionOrder.h"
#include "swift/SILOptimizer/Analysis/ValueTracking.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "swift/SILOptimizer/Utils/SILInliner.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

using namespace swift;

STATISTIC(NumClosureSpecialized,
          "Number of functions with closures specialized");
STATISTIC(NumPropagatedClosuresEliminated,
          "Number of closures propagated and then eliminated");
STATISTIC(NumPropagatedClosuresNotEliminated,
          "Number of closures propagated but not eliminated");

llvm::cl::opt<bool> EliminateDeadClosures(
    "closure-specialize-eliminate-dead-closures", llvm::cl::init(true),
    llvm::cl::desc("Do not eliminate dead closures after closure "
                   "specialization. This is meant ot be used when testing."));

llvm::cl::opt<bool> SupportGenericClosureSpecialization(
    "closure-specialize-generic-closures", llvm::cl::init(false),
    llvm::cl::desc("Support generic closures during closure "
                   "specialization. This is meant ot be used when testing."));
//===----------------------------------------------------------------------===//
//                                  Utility
//===----------------------------------------------------------------------===//

static bool isSupportedClosureKind(const SILInstruction *I) {
  return isa<ThinToThickFunctionInst>(I) || isa<PartialApplyInst>(I);
}

//===----------------------------------------------------------------------===//
//                       Closure Spec Cloner Interface
//===----------------------------------------------------------------------===//

namespace {

class CallSiteDescriptor;

/// \brief A SILCloner subclass which clones a function that takes a closure
/// argument. We update the parameter list to remove the parameter for the
/// closure argument and to append the variables captured in the closure.
/// We also need to replace the closure parameter with the partial apply
/// on the closure. We need to update the callsite to pass in the correct
/// arguments.
class ClosureSpecCloner : public SILClonerWithScopes<ClosureSpecCloner> {
public:
  using SuperTy = SILClonerWithScopes<ClosureSpecCloner>;
  friend class SILVisitor<ClosureSpecCloner>;
  friend class SILCloner<ClosureSpecCloner>;

  ClosureSpecCloner(const CallSiteDescriptor &CallSiteDesc,
                    StringRef ClonedName,
                    SubstitutionMap &CallerToClosureUserSubsMap,
                    SubstitutionMap &OldToNewCalleeSubsMap);

  void populateCloned();

  SILFunction *getCloned() { return &getBuilder().getFunction(); }
  static SILFunction *cloneFunction(const CallSiteDescriptor &CallSiteDesc,
                                    StringRef NewName);

  void postProcess(SILInstruction *Orig, SILInstruction *Cloned) {
    SILClonerWithScopes<ClosureSpecCloner>::postProcess(Orig, Cloned);
  }

  const SILDebugScope *remapScope(const SILDebugScope *DS) {
    return SILClonerWithScopes<ClosureSpecCloner>::remapScope(DS);
  }

  SILType remapType(SILType Ty);

  CanType remapASTType(CanType ty) {
    return ty.subst(CallerToClosureUserSubsMap)
        .subst(OldToNewCalleeSubsMap)
        ->getCanonicalType();
  }

  SubstitutionMap &getCallerToClosureUserSubsMap() {
    return CallerToClosureUserSubsMap;
  }

private:
  static SILFunction *initCloned(const CallSiteDescriptor &CallSiteDesc,
                                 StringRef ClonedName,
                                 SubstitutionMap &CallerToClosureUserSubsMap,
                                 SubstitutionMap &OldToNewCalleeSubsMap);
  static SubstitutionMap
  computeCallerToClosureUserSubsMap(SILFunction *Caller, SILFunction *Callee,
                                    SubstitutionList Subs,
                                    SILFunction *NewCallee = nullptr);
  static void
  computeOldToNewCalleeSubsMap(SILFunction *Old, SILFunction *New,
                               SubstitutionMap &OldToNewCalleeSubsMap);
  const CallSiteDescriptor &CallSiteDesc;
  // Map archetypes of the function containg the apply instruction to the
  // archetypes of the closure user.
  SubstitutionMap &CallerToClosureUserSubsMap;
  // Map archetypes of the original ClosureUser to the archetypes of the cloned
  // ClosureUser.
  SubstitutionMap &OldToNewCalleeSubsMap;
};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
//                            Call Site Descriptor
//===----------------------------------------------------------------------===//

namespace {
struct ClosureInfo;

class CallSiteDescriptor {
  ClosureInfo *CInfo;
  FullApplySite AI;
  unsigned ClosureIndex;
  SILParameterInfo ClosureParamInfo;

  // This is only needed if we have guaranteed parameters. In most cases it will
  // have only one element, a return inst.
  llvm::TinyPtrVector<SILBasicBlock *> NonFailureExitBBs;

public:
  CallSiteDescriptor(ClosureInfo *CInfo, FullApplySite AI,
                     unsigned ClosureIndex, SILParameterInfo ClosureParamInfo,
                     llvm::TinyPtrVector<SILBasicBlock *> &&NonFailureExitBBs)
    : CInfo(CInfo), AI(AI), ClosureIndex(ClosureIndex),
      ClosureParamInfo(ClosureParamInfo),
      NonFailureExitBBs(NonFailureExitBBs) {}

  CallSiteDescriptor(CallSiteDescriptor&&) =default;
  CallSiteDescriptor &operator=(CallSiteDescriptor &&) =default;

  SILFunction *getApplyCallee() const {
    return cast<FunctionRefInst>(AI.getCallee())->getReferencedFunction();
  }

  SILFunction *getClosureCallee() const {
    if (auto *PAI = dyn_cast<PartialApplyInst>(getClosure()))
      return cast<FunctionRefInst>(PAI->getCallee())->getReferencedFunction();

    auto *TTTFI = cast<ThinToThickFunctionInst>(getClosure());
    return cast<FunctionRefInst>(TTTFI->getCallee())->getReferencedFunction();
  }

  bool closureHasRefSemanticContext() const {
    return isa<PartialApplyInst>(getClosure());
  }

  unsigned getClosureIndex() const { return ClosureIndex; }

  SILParameterInfo getClosureParameterInfo() const { return ClosureParamInfo; }

  SILInstruction *
  createNewClosure(SILBuilder &B, SILValue V,
                   ArrayRef<SILValue> Args, ClosureSpecCloner &C) const {
    if (isa<PartialApplyInst>(getClosure())) {
      auto ClosedOverFun = getClosureCallee();
      auto PAI = cast<PartialApplyInst>(getClosure());
      auto FnTy = dyn_cast<SILFunctionType>(V->getType().getSwiftRValueType());
      assert(!FnTy->getGenericSignature() ||
             !FnTy->getGenericSignature()->getSubstitutableParams().size() ||
             PAI->getSubstitutions().size() ==
                 FnTy->getGenericSignature()->getSubstitutableParams().size());

      SmallVector<Substitution, 2> NewSubs;
      auto NewClosureType = getClosure()->getType();
      auto SubstCanFnTy = V->getType().castTo<SILFunctionType>();

      // Handle invocations of generic closures.
      if (PAI->hasSubstitutions()) {
        auto ClosedOverFunSig =
          ClosedOverFun->getLoweredFunctionType()->getGenericSignature();

        auto PAISubs = PAI->getSubstitutions();
        auto PAISubsMap = ClosedOverFunSig->getSubstitutionMap(PAISubs);

        // Replace all archetypes from the apply's function by archetypes
        // of the apply's callee.
        auto NewPAISubsMap = PAISubsMap.subst(
            QuerySubstitutionMap{C.getCallerToClosureUserSubsMap()},
            [&](CanType dependentType, Type conformingReplacementType,
                ProtocolType *conformedProtocol)
                -> Optional<ProtocolConformanceRef> {
              assert(conformingReplacementType->is<ArchetypeType>());
              return ProtocolConformanceRef(conformedProtocol->getDecl());
            });
        ClosedOverFunSig->getSubstitutions(NewPAISubsMap, NewSubs);
        // Remap the type of the closure.
        NewClosureType = C.remapType(getClosure()->getType());
        auto &M = getApplyInst().getModule();
        SubstCanFnTy = SubstCanFnTy->substGenericArgs(M, NewPAISubsMap);
      }
      auto SILSubstFnTy = SILType::getPrimitiveObjectType(SubstCanFnTy);

      return B.createPartialApply(getClosure()->getLoc(), V, SILSubstFnTy,
                                  NewSubs, Args, NewClosureType);
    }
    assert(isa<ThinToThickFunctionInst>(getClosure()) &&
           "We only support partial_apply and thin_to_thick_function");
    return B.createThinToThickFunction(getClosure()->getLoc(), V,
                                       getClosure()->getType());
  }

  FullApplySite getApplyInst() const { return AI; }

  IsFragile_t isFragile() const;

  std::string createName() const;

  OperandValueArrayRef getArguments() const {
    if (auto *PAI = dyn_cast<PartialApplyInst>(getClosure()))
      return PAI->getArguments();

    // Thin to thick function has no non-callee arguments.
    assert(isa<ThinToThickFunctionInst>(getClosure()) &&
           "We only support partial_apply and thin_to_thick_function");
    return OperandValueArrayRef(ArrayRef<Operand>());
  }

  inline SILInstruction *getClosure() const;

  unsigned getNumArguments() const {
    if (auto *PAI = dyn_cast<PartialApplyInst>(getClosure()))
      return PAI->getNumArguments();

    // Thin to thick function has no non-callee arguments.
    assert(isa<ThinToThickFunctionInst>(getClosure()) &&
           "We only support partial_apply and thin_to_thick_function");
    return 0;
  }

  bool isClosureGuaranteed() const {
    return getClosureParameterInfo().isGuaranteed();
  }

  bool isClosureConsumed() const {
    return getClosureParameterInfo().isConsumed();
  }

  SILLocation getLoc() const { return getClosure()->getLoc(); }

  SILModule &getModule() const { return AI.getModule(); }

  SubstitutionList getSubstitutions() const { return AI.getSubstitutions(); }

  ArrayRef<SILBasicBlock *> getNonFailureExitBBs() const {
    return NonFailureExitBBs;
  }

  /// Extend the lifetime of 'Arg' to the lifetime of the closure.
  void extendArgumentLifetime(SILValue Arg) const;
};
} // end anonymous namespace

namespace {
struct ClosureInfo {
  SILInstruction *Closure;
  ValueLifetimeAnalysis::Frontier LifetimeFrontier;
  llvm::SmallVector<CallSiteDescriptor, 8> CallSites;

  ClosureInfo(SILInstruction *Closure): Closure(Closure) {}

  ClosureInfo(ClosureInfo &&) =default;
  ClosureInfo &operator=(ClosureInfo &&) =default;
};
} // end anonymous namespace

SILInstruction *CallSiteDescriptor::getClosure() const {
  return CInfo->Closure;
}

SILFunction *
ClosureSpecCloner::cloneFunction(const CallSiteDescriptor &CallSiteDesc,
                                 StringRef NewName) {
  SubstitutionMap CallerToClosureUserSubsMap(computeCallerToClosureUserSubsMap(
      CallSiteDesc.getApplyInst().getFunction(), CallSiteDesc.getApplyCallee(),
      CallSiteDesc.getSubstitutions()));
  SubstitutionMap OldToNewCalleeSubsMap;
  ClosureSpecCloner C(CallSiteDesc, NewName, CallerToClosureUserSubsMap, OldToNewCalleeSubsMap);
  C.populateCloned();
  ++NumClosureSpecialized;
  return C.getCloned();
};

SubstitutionMap ClosureSpecCloner::computeCallerToClosureUserSubsMap(
    SILFunction *Caller, SILFunction *Callee, SubstitutionList CalleeSubs,
    SILFunction *NewCallee) {
  SubstitutionMap SubsMap;
  if (CalleeSubs.empty())
    return SubsMap;

  if (!NewCallee)
    NewCallee = Callee;

  // Generic signatures of Callee and NewCallee are supposed to have the
  // same number of generic parameters. Only the set of requirements on
  // their generic parameters is different.
  assert(NewCallee->getLoweredFunctionType()
             ->getGenericSignature()
             ->getGenericParams()
             .size() ==
         Callee->getLoweredFunctionType()
             ->getGenericSignature()
             ->getGenericParams()
             .size());

  auto GenericEnv = Caller->getGenericEnvironment();
  auto GenericSig = Caller->getLoweredFunctionType()->getGenericSignature();

  auto CalleeGenericSig =
      Callee->getLoweredFunctionType()->getGenericSignature();

  SubstitutionMap CalleeSubsMap;
  ArrayRef<GenericTypeParamType *> CalleeGenericParams;
  if (CalleeGenericSig) {
    CalleeSubsMap = CalleeGenericSig->getSubstitutionMap(CalleeSubs);
    CalleeGenericParams = CalleeGenericSig->getSubstitutableParams();
  }

  if (GenericEnv) {
    // Map archetypes of the caller containing the apply instruction to the
    // archetypes of the apply's callee.
    // TODO: We also need to form proper conformances, as required by the
    // closure.
    SubsMap = GenericEnv->getSubstitutionMap(
        [&](Type ty) -> Type {
          assert(ty->is<ArchetypeType>());
          for (auto GP : CalleeGenericParams) {
            auto GPArchetype =
                NewCallee->mapTypeIntoContext(GP->getCanonicalType());
            auto GPSubstTy = GP->getCanonicalType().subst(CalleeSubsMap);
            // Return the callee's archetype if its interface type is mapped
            // to the current archetype from the GenericEnv.
            if (GPSubstTy->getCanonicalType() == ty->getCanonicalType()) {
              return GPArchetype;
            }
          }
          return ty;
        },
        LookUpConformanceInSignature(*GenericSig));
  }

  return SubsMap;
}

/// Build a SubsitutionMap that substitutes archetypes of the
/// original function Old by archetypes of the cloned function New.
void ClosureSpecCloner::computeOldToNewCalleeSubsMap(
    SILFunction *Old, SILFunction *New,
    SubstitutionMap &OldToNewCalleeSubsMap) {
  // Generic signatures of Callee and NewCallee are supposed to have the
  // same number of generic parameters. Only the set of requirements on
  // their generic parameters is different.
  assert(New->getLoweredFunctionType()
             ->getGenericSignature()
             ->getGenericParams()
             .size() ==
         Old->getLoweredFunctionType()
             ->getGenericSignature()
             ->getGenericParams()
             .size());

  auto OldGenericEnv = Old->getGenericEnvironment();
  auto OldGenericSig = Old->getLoweredFunctionType()->getGenericSignature();
  auto NewGenericEnv = New->getGenericEnvironment();

  // TODO: We also need to form proper conformances, as required by the
  // closure.
  OldToNewCalleeSubsMap = OldGenericEnv->getSubstitutionMap(
      [&](Type ty) -> Type {
        assert(ty->is<ArchetypeType>());
        return NewGenericEnv->mapTypeIntoContext(
            OldGenericEnv->mapTypeOutOfContext(ty));
      },
      LookUpConformanceInSignature(*OldGenericSig));
}

ClosureSpecCloner::ClosureSpecCloner(
    const CallSiteDescriptor &CallSiteDesc, StringRef ClonedName,
    SubstitutionMap &CallerToClosureUserSubsMap,
    SubstitutionMap &OldToNewCalleeSubsMap)
    : SuperTy(*initCloned(CallSiteDesc, ClonedName, CallerToClosureUserSubsMap,
                          OldToNewCalleeSubsMap)),
      CallSiteDesc(CallSiteDesc),
      CallerToClosureUserSubsMap(CallerToClosureUserSubsMap),
      OldToNewCalleeSubsMap(OldToNewCalleeSubsMap) {}

SILType ClosureSpecCloner::remapType(SILType Ty) {
  return Ty
      .subst(CallSiteDesc.getApplyInst().getModule(),
             CallerToClosureUserSubsMap)
      .subst(CallSiteDesc.getApplyInst().getModule(),
             OldToNewCalleeSubsMap);
}

/// Update the callsite to pass in the correct arguments.
static void rewriteApplyInst(const CallSiteDescriptor &CSDesc,
                             SILFunction *NewF) {
  FullApplySite AI = CSDesc.getApplyInst();
  SILInstruction *Closure = CSDesc.getClosure();
  SILBuilderWithScope Builder(Closure);
  FunctionRefInst *FRI = Builder.createFunctionRef(AI.getLoc(), NewF);

  // Create the args for the new apply by removing the closure argument...
  llvm::SmallVector<SILValue, 8> NewArgs;
  unsigned Index = 0;
  for (auto Arg : AI.getArguments()) {
    if (Index != CSDesc.getClosureIndex())
      NewArgs.push_back(Arg);
    Index++;
  }

  // ... and appending the captured arguments. We also insert retains here at
  // the location of the original closure. This is needed to balance the
  // implicit release of all captured arguments that occurs when the partial
  // apply is destroyed.
  SILModule &M = NewF->getModule();
  for (auto Arg : CSDesc.getArguments()) {
    NewArgs.push_back(Arg);

    SILType ArgTy = Arg->getType();

    // If our argument is of trivial type, continue...
    if (ArgTy.isTrivial(M))
      continue;

    // TODO: When we support address types, this code path will need to be
    // updated.

    // We need to balance the consumed argument of the new partial_apply in the
    // specialized callee by a retain. If both the original partial_apply and
    // the apply of the callee are in the same basic block we can assume they
    // are executed the same number of times. Therefore it is sufficient to just
    // retain the argument at the site of the original partial_apply.
    //
    //    %closure = partial_apply (%arg)
    //             = apply %callee(%closure)
    //  =>
    //             retain %arg
    //    %closure = partial_apply (%arg)
    //               apply %specialized_callee(..., %arg)
    //
    // However, if they are not in the same basic block the callee might be
    // executed more frequently than the closure (for example, if the closure is
    // created in a loop preheader and the callee taking the closure is executed
    // in the loop). In such a case we must keep the argument live across the
    // call site of the callee and emit a matching retain for every invocation
    // of the callee.
    //
    //    %closure = partial_apply (%arg)
    //
    //    while () {
    //             = %callee(%closure)
    //    }
    // =>
    //               retain %arg
    //    %closure = partial_apply (%arg)
    //
    //    while () {
    //               retain %arg
    //               apply %specialized_callee(.., %arg)
    //    }
    //               release %arg
    //
    if (AI.getParent() != Closure->getParent()) {
      // Emit the retain and release that keeps the argument life across the
      // callee using the closure.
      CSDesc.extendArgumentLifetime(Arg);

      // Emit the retain that matches the captured argument by the partial_apply
      // in the callee that is consumed by the partial_apply.
      Builder.setInsertionPoint(AI.getInstruction());
      Builder.createRetainValue(Closure->getLoc(), Arg, Builder.getDefaultAtomicity());
    } else {
      Builder.createRetainValue(Closure->getLoc(), Arg, Builder.getDefaultAtomicity());
    }
  }

  SILType LoweredType = NewF->getLoweredType();
  auto loweredConv = NewF->getConventions();
  SILType ResultType = loweredConv.getSILResultType();
  Builder.setInsertionPoint(AI.getInstruction());
  FullApplySite NewAI;
  // The generic signature of the ClosureUser may have changed,
  // because it may have more requirements now. Therefore,
  // the list of substitutions may need to be updated to contain
  // more conformances.
  auto Subs = CSDesc.getSubstitutions();
  auto NewSubstFnTy = LoweredType;
  SmallVector<Substitution, 4> NewSubs;
  if (!Subs.empty()) {
    auto SubsMap = CSDesc.getApplyCallee()
                       ->getLoweredFunctionType()
                       ->getGenericSignature()
                       ->getSubstitutionMap(Subs);

    NewSubstFnTy = SILType::getPrimitiveObjectType(
        LoweredType.castTo<SILFunctionType>()->substGenericArgs(
            M, QuerySubstitutionMap{SubsMap},
            // Add any required abstract conformances.
            [&](CanType dependentType, Type conformingReplacementType,
                ProtocolType *conformedProtocol)
                -> Optional<ProtocolConformanceRef> {
              assert(conformingReplacementType->is<ArchetypeType>());
              return ProtocolConformanceRef(conformedProtocol->getDecl());
            }));

    auto NewGenericSig = NewF->getLoweredFunctionType()->getGenericSignature();
    NewGenericSig->getSubstitutions(
        QuerySubstitutionMap{SubsMap},
        LookUpConformanceInSignature(*NewGenericSig), NewSubs);
    Subs = NewSubs;
  }
  if (auto *TAI = dyn_cast<TryApplyInst>(AI)) {
    NewAI = Builder.createTryApply(AI.getLoc(), FRI, NewSubstFnTy,
                                   Subs,
                                   NewArgs,
                                   TAI->getNormalBB(), TAI->getErrorBB());
    // If we passed in the original closure as @owned, then insert a release
    // right after NewAI. This is to balance the +1 from being an @owned
    // argument to AI.
    if (CSDesc.isClosureConsumed() && CSDesc.closureHasRefSemanticContext()) {
      Builder.setInsertionPoint(TAI->getNormalBB()->begin());
      Builder.createReleaseValue(Closure->getLoc(), Closure, Builder.getDefaultAtomicity());
      Builder.setInsertionPoint(TAI->getErrorBB()->begin());
      Builder.createReleaseValue(Closure->getLoc(), Closure, Builder.getDefaultAtomicity());
      Builder.setInsertionPoint(AI.getInstruction());
    }
  } else {
    NewAI = Builder.createApply(AI.getLoc(), FRI, NewSubstFnTy,
                                ResultType, Subs,
                                NewArgs, cast<ApplyInst>(AI)->isNonThrowing());
    // If we passed in the original closure as @owned, then insert a release
    // right after NewAI. This is to balance the +1 from being an @owned
    // argument to AI.
    if (CSDesc.isClosureConsumed() && CSDesc.closureHasRefSemanticContext())
      Builder.createReleaseValue(Closure->getLoc(), Closure, Builder.getDefaultAtomicity());
  }

  // Replace all uses of the old apply with the new apply.
  if (isa<ApplyInst>(AI))
    AI.getInstruction()->replaceAllUsesWith(NewAI.getInstruction());
  // Erase the old apply.
  AI.getInstruction()->eraseFromParent();

  // TODO: Maybe include invalidation code for CallSiteDescriptor after we erase
  // AI from parent?
}

IsFragile_t CallSiteDescriptor::isFragile() const {
  if (getClosure()->getFunction()->isFragile() &&
      getApplyCallee()->isFragile())
    return IsFragile;
  return IsNotFragile;
}

std::string CallSiteDescriptor::createName() const {
  Mangle::Mangler M;
  auto P = Demangle::SpecializationPass::ClosureSpecializer;
  FunctionSignatureSpecializationMangler OldFSSM(P, M, isFragile(),
                                                 getApplyCallee());
  NewMangling::FunctionSignatureSpecializationMangler NewFSSM(P, isFragile(),
                                                              getApplyCallee());

  if (auto *PAI = dyn_cast<PartialApplyInst>(getClosure())) {
    OldFSSM.setArgumentClosureProp(getClosureIndex(), PAI);
    NewFSSM.setArgumentClosureProp(getClosureIndex(), PAI);
  } else {
    auto *TTTFI = cast<ThinToThickFunctionInst>(getClosure());
    OldFSSM.setArgumentClosureProp(getClosureIndex(), TTTFI);
    NewFSSM.setArgumentClosureProp(getClosureIndex(), TTTFI);
  }
  OldFSSM.mangle();
  std::string Old = M.finalize();
  std::string New = NewFSSM.mangle();
  return NewMangling::selectMangling(Old, New);
}

void CallSiteDescriptor::extendArgumentLifetime(SILValue Arg) const {
  assert(!CInfo->LifetimeFrontier.empty() &&
         "Need a post-dominating release(s)");

  // Extend the lifetime of a captured argument to cover the callee.
  SILBuilderWithScope Builder(getClosure());
  Builder.createRetainValue(getClosure()->getLoc(), Arg, Builder.getDefaultAtomicity());
  for (auto *I : CInfo->LifetimeFrontier) {
    Builder.setInsertionPoint(I);
    Builder.createReleaseValue(getClosure()->getLoc(), Arg, Builder.getDefaultAtomicity());
  }
}

static bool isSupportedClosure(const SILInstruction *Closure) {
  if (!isSupportedClosureKind(Closure))
    return false;

  // We only support simple closures where a partial_apply or
  // thin_to_thick_function is passed a function_ref. This will be stored here
  // so the checking of the Callee can use the same code in both cases.
  SILValue Callee;

  // If Closure is a partial apply...
  if (auto *PAI = dyn_cast<PartialApplyInst>(Closure)) {
    // And it has substitutions, return false.
    if (!SupportGenericClosureSpecialization && PAI->hasSubstitutions())
      return false;

    // If any arguments are not objects, return false. This is a temporary
    // limitation.
    for (SILValue Arg : PAI->getArguments())
      if (!Arg->getType().isObject())
        return false;

    // Ok, it is a closure we support, set Callee.
    Callee = PAI->getCallee();

  } else {
    // Otherwise closure must be a thin_to_thick_function.
    Callee = cast<ThinToThickFunctionInst>(Closure)->getCallee();
  }

  // Make sure that it is a simple partial apply (i.e. its callee is a
  // function_ref).
  //
  // TODO: We can probably handle other partial applies here.
  auto *FRI = dyn_cast<FunctionRefInst>(Callee);
  if (!FRI)
    return false;

  // Otherwise, we do support specializing this closure.
  return true;
}

//===----------------------------------------------------------------------===//
//                     Closure Spec Cloner Implementation
//===----------------------------------------------------------------------===//

/// Create a new generic signature, because it may need
/// some additional requirements, e.g. if they are present in the
/// ClosedOverFun's generic signature, but are not present in the ClosureUser's
/// generic signature.
/// The new signature has the same generic parameters as the old signature of
/// the ClosureUser, but eventually it has more requirements.
static std::pair<GenericEnvironment *, CanGenericSignature>
createNewGenericEnvironementAndSignature(
    const CallSiteDescriptor &CallSiteDesc,
    const SubstitutionMap &CallerToClosureUserSubsMap) {
  SILFunction *ClosedOverFun = CallSiteDesc.getClosureCallee();
  auto ClosedOverFunTy = ClosedOverFun->getLoweredFunctionType();
  SILFunction *ClosureUser = CallSiteDesc.getApplyCallee();
  auto ClosureUserFunTy = ClosureUser->getLoweredFunctionType();
  auto ClosureUserGenericSig = ClosureUserFunTy->getGenericSignature();
  auto ClosedOverFunGenericSig = ClosedOverFunTy->getGenericSignature();
  auto &M = ClosureUser->getModule();

  GenericSignatureBuilder GSB(M.getASTContext(),
                              LookUpConformanceInModule(M.getSwiftModule()));

  // First, add the generics signature of the ClosureUser.
  GSB.addGenericSignature(ClosureUserGenericSig);

  // Then add any additional requirements from the ClosedOverFun.
  auto Closure = CallSiteDesc.getClosure();
  auto PAI = dyn_cast<PartialApplyInst>(Closure);
  assert(PAI);
  auto PAISubs = PAI->getSubstitutions();
  auto PAISubsMap = ClosedOverFunGenericSig->getSubstitutionMap(PAISubs);
  auto Source =
      GenericSignatureBuilder::FloatingRequirementSource::forAbstract();

  // Express the requirements of the Closure in terms of the ClosureUser's
  // interface types and add these requirements.
  // Re-mapping of the types is done in two steps:
  // - First map types to the ClosureUser's archetypes
  // - Then map them to the ClosureUser's interface
  for (auto Req : ClosedOverFunGenericSig->getRequirements()) {
    switch (Req.getKind()) {
    case swift::RequirementKind::SameType:
    case swift::RequirementKind::Conformance:
    case swift::RequirementKind::Superclass: {
      auto First = Req.getFirstType()
                       .subst(PAISubsMap)
                       .subst(CallerToClosureUserSubsMap);
      auto Second = Req.getSecondType()
                        .subst(PAISubsMap)
                        .subst(CallerToClosureUserSubsMap);
      // If everything is concrete, the requirement can be ommitted.
      if (!First->hasArchetype() && !Second->hasArchetype())
        continue;
      Requirement NewReq(Req.getKind(),
                         ClosureUser->mapTypeOutOfContext(First),
                         ClosureUser->mapTypeOutOfContext(Second));
      GSB.addRequirement(NewReq, Source);
      break;
    }
    case swift::RequirementKind::Layout: {
      auto First = Req.getFirstType()
                       .subst(PAISubsMap)
                       .subst(CallerToClosureUserSubsMap);
      // If everything is concrete, the requirement can be ommitted.
      if (!First->hasArchetype())
        continue;
      Requirement NewReq(Req.getKind(),
                         ClosureUser->mapTypeOutOfContext(First),
                         Req.getLayoutConstraint());
      GSB.addRequirement(NewReq, Source);
      break;
    }
    }
  }

  GSB.finalize(SourceLoc(), ClosureUserGenericSig->getGenericParams(),
               /* allowConcreteGenericParams */ true);
  auto ClonedGenericSig = GSB.getGenericSignature()->getCanonicalSignature();
  auto *ClonedGenericEnv =
      ClonedGenericSig->createGenericEnvironment(*M.getSwiftModule());
  return std::make_pair(ClonedGenericEnv, ClonedGenericSig);
}

/// In this function we create the actual cloned function and its proper cloned
/// type. But we do not create any body. This implies that the creation of the
/// actual arguments in the function is in populateCloned.
///
/// \arg ClonedName The name of the cloned function that we will create.
SILFunction *
ClosureSpecCloner::initCloned(const CallSiteDescriptor &CallSiteDesc,
                              StringRef ClonedName,
                              SubstitutionMap &CallerToClosureUserSubsMap,
                              SubstitutionMap &OldToNewCalleeSubsMap) {
  SILFunction *ClosureUser = CallSiteDesc.getApplyCallee();

  // This is the list of new interface parameters of the cloned function.
  llvm::SmallVector<SILParameterInfo, 4> NewParameterInfoList;

  // First add to NewParameterInfoList all of the SILParameterInfo in the
  // original function except for the closure.
  CanSILFunctionType ClosureUserFunTy = ClosureUser->getLoweredFunctionType();
  auto ClosureUserConv = ClosureUser->getConventions();
  unsigned Index = ClosureUserConv.getSILArgIndexOfFirstParam();
  for (auto &param : ClosureUserConv.getParameters()) {
    if (Index != CallSiteDesc.getClosureIndex())
      NewParameterInfoList.push_back(param);
    ++Index;
  }

  // Then add any arguments that are captured in the closure to the function's
  // argument type. Since they are captured, we need to pass them directly into
  // the new specialized function.

  SILModule &M = ClosureUser->getModule();
  SILFunction *ClosedOverFun = CallSiteDesc.getClosureCallee();
  auto ClosedOverFunTy = ClosedOverFun->getLoweredFunctionType();

  // An artificial scope just for the sake of GenericContextScope.
  {
    CanGenericSignature CanSig;
    if (ClosedOverFunTy->getGenericSignature())
      CanSig = ClosedOverFunTy->getGenericSignature()->getCanonicalSignature();

    // Set a proper generic context, because it is needed by the
    // type lowering, e.g. when it evaluates isTrivial, etc.
    Lowering::GenericContextScope GenericScope(M.Types, CanSig);

    auto ClosedOverFunConv = ClosedOverFun->getConventions();

    // Captured parameters are always appended to the function signature. If the
    // type of the captured argument is trivial, pass the argument as
    // Direct_Unowned. Otherwise pass it as Direct_Owned.
    //
    // We use the type of the closure here since we allow for the closure to be
    // an
    // external declaration.
    unsigned NumTotalParams = ClosedOverFunConv.getNumParameters();
    unsigned NumNotCaptured = NumTotalParams - CallSiteDesc.getNumArguments();
    for (auto &PInfo :
         ClosedOverFunConv.getParameters().slice(NumNotCaptured)) {
      if (ClosedOverFunConv.getSILType(PInfo).isTrivial(M)) {
        SILParameterInfo NewPInfo(PInfo.getType(),
                                  ParameterConvention::Direct_Unowned);
        NewParameterInfoList.push_back(NewPInfo);
        continue;
      }

      SILParameterInfo NewPInfo(PInfo.getType(),
                                ParameterConvention::Direct_Owned);
      NewParameterInfoList.push_back(NewPInfo);
    }
  }

  // The specialized function is always a thin function. This is important
  // because we may add additional parameters after the Self parameter of
  // witness methods. In this case the new function is not a method anymore.
  auto ExtInfo = ClosureUserFunTy->getExtInfo();
  ExtInfo = ExtInfo.withRepresentation(SILFunctionTypeRepresentation::Thin);

  auto ClosureUserGenericSig = ClosureUserFunTy->getGenericSignature();
  auto ClosedOverFunGenericSig = ClosedOverFunTy->getGenericSignature();
  auto ClonedGenericSig = ClosureUserGenericSig;
  auto ClonedGenericEnv = ClosureUser->getGenericEnvironment();
  bool CreatedNewGenericEnv = false;

  // A new generic signature should be created, because it may need
  // some additional requirements.
  if (ClosedOverFunGenericSig &&
      !ClosedOverFunGenericSig->getRequirements().empty()) {
    std::tie(ClonedGenericEnv, ClonedGenericSig) =
        createNewGenericEnvironementAndSignature(CallSiteDesc,
                                                 CallerToClosureUserSubsMap);
    CreatedNewGenericEnv = true;
  }

  auto ClonedTy = SILFunctionType::get(
      ClonedGenericSig, ExtInfo,
      ClosureUserFunTy->getCalleeConvention(), NewParameterInfoList,
      ClosureUserFunTy->getResults(),
      ClosureUserFunTy->getOptionalErrorResult(), M.getASTContext());

  // We make this function bare so we don't have to worry about decls in the
  // SILArgument.
  auto *Fn = M.createFunction(
      // It's important to use a shared linkage for the specialized function
      // and not the original linkage.
      // Otherwise the new function could have an external linkage (in case the
      // original function was de-serialized) and would not be code-gen'd.
      getSpecializedLinkage(ClosureUser, ClosureUser->getLinkage()), ClonedName,
      ClonedTy, ClonedGenericEnv, ClosureUser->getLocation(), IsBare,
      ClosureUser->isTransparent(), CallSiteDesc.isFragile(),
      ClosureUser->isThunk(), ClosureUser->getClassVisibility(),
      ClosureUser->getInlineStrategy(), ClosureUser->getEffectsKind(),
      ClosureUser, ClosureUser->getDebugScope());
  if (ClosureUser->hasUnqualifiedOwnership()) {
    Fn->setUnqualifiedOwnership();
  }
  for (auto &Attr : ClosureUser->getSemanticsAttrs())
    Fn->addSemanticsAttr(Attr);

  // SubstitutionMaps need to be recomputed if a new generic environment was
  // created.
  if (CreatedNewGenericEnv) {
    auto TmpSubsMap = computeCallerToClosureUserSubsMap(
        CallSiteDesc.getApplyInst().getFunction(), ClosureUser,
        CallSiteDesc.getSubstitutions(), Fn);
    CallerToClosureUserSubsMap = TmpSubsMap;
    // Now update the old to new callee SubMap.
    computeOldToNewCalleeSubsMap(ClosureUser, Fn, OldToNewCalleeSubsMap);
  }

  return Fn;
}

/// \brief Populate the body of the cloned closure, modifying instructions as
/// necessary. This is where we create the actual specialized BB Arguments.
void ClosureSpecCloner::populateCloned() {
  SILFunction *Cloned = getCloned();
  SILFunction *ClosureUser = CallSiteDesc.getApplyCallee();

  // Create arguments for the entry block.
  SILBasicBlock *ClosureUserEntryBB = &*ClosureUser->begin();
  SILBasicBlock *ClonedEntryBB = Cloned->createBasicBlock();

  // Remove the closure argument.
  SILArgument *ClosureArg = nullptr;
  for (size_t i = 0, e = ClosureUserEntryBB->args_size(); i != e; ++i) {
    SILArgument *Arg = ClosureUserEntryBB->getArgument(i);
    if (i == CallSiteDesc.getClosureIndex()) {
      ClosureArg = Arg;
      continue;
    }

    // Otherwise, create a new argument which copies the original argument.
    auto ArgSILType = Arg->getType();
    auto ArgCanType = Cloned
                          ->mapTypeIntoContext(ClosureUser->mapTypeOutOfContext(
                              ArgSILType.getSwiftRValueType()))
                          ->getCanonicalType();
    ArgSILType = SILType::getPrimitiveType(ArgCanType,
                                           ArgSILType.getCategory());
    assert(!ArgSILType.getSwiftRValueType()->hasTypeParameter());
    SILValue MappedValue =
        ClonedEntryBB->createFunctionArgument(ArgSILType, Arg->getDecl());
    ValueMap.insert(std::make_pair(Arg, MappedValue));
  }

  // Next we need to add in any arguments that are not captured as arguments to
  // the cloned function.
  //
  // We do not insert the new mapped arguments into the value map since there by
  // definition is nothing in the partial apply user function that references
  // such arguments. After this pass is done the only thing that will reference
  // the arguments is the partial apply that we will create.
  SILFunction *ClosedOverFun = CallSiteDesc.getClosureCallee();
  auto ClosedOverFunConv = ClosedOverFun->getConventions();
  unsigned NumTotalParams = ClosedOverFunConv.getNumParameters();
  unsigned NumNotCaptured = NumTotalParams - CallSiteDesc.getNumArguments();
  llvm::SmallVector<SILValue, 4> NewPAIArgs;
  for (auto &PInfo : ClosedOverFunConv.getParameters().slice(NumNotCaptured)) {
    auto paramTy = ClosedOverFunConv.getSILType(PInfo);
    // Map to a contextual type.
    paramTy = SILType::getPrimitiveType(
        Cloned->mapTypeIntoContext(paramTy.getSwiftRValueType())
            ->getCanonicalType(),
        paramTy.getCategory());
    assert(!paramTy.getSwiftRValueType()->hasTypeParameter());
    SILValue MappedValue = ClonedEntryBB->createFunctionArgument(paramTy);
    NewPAIArgs.push_back(MappedValue);
  }

  SILBuilder &Builder = getBuilder();
  Builder.setInsertionPoint(ClonedEntryBB);

  // Clone FRI and PAI, and replace usage of the removed closure argument
  // with result of cloned PAI.
  SILValue FnVal =
      Builder.createFunctionRef(CallSiteDesc.getLoc(), ClosedOverFun);
  auto *NewClosure =
      CallSiteDesc.createNewClosure(Builder, FnVal, NewPAIArgs, *this);
  ValueMap.insert(std::make_pair(ClosureArg, SILValue(NewClosure)));

  BBMap.insert(std::make_pair(ClosureUserEntryBB, ClonedEntryBB));
  // Recursively visit original BBs in depth-first preorder, starting with the
  // entry block, cloning all instructions other than terminators.
  visitSILBasicBlock(ClosureUserEntryBB);

  // Now iterate over the BBs and fix up the terminators.
  for (auto BI = BBMap.begin(), BE = BBMap.end(); BI != BE; ++BI) {
    Builder.setInsertionPoint(BI->second);
    visit(BI->first->getTerminator());
  }

  // Then insert a release in all non failure exit BBs if our partial apply was
  // guaranteed. This is b/c it was passed at +0 originally and we need to
  // balance the initial increment of the newly created closure.
  if (CallSiteDesc.isClosureGuaranteed() &&
      CallSiteDesc.closureHasRefSemanticContext()) {
    for (SILBasicBlock *BB : CallSiteDesc.getNonFailureExitBBs()) {
      SILBasicBlock *OpBB = BBMap[BB];

      TermInst *TI = OpBB->getTerminator();
      auto Loc = CleanupLocation::get(NewClosure->getLoc());

      // If we have a return, we place the release right before it so we know
      // that it will be executed at the end of the epilogue.
      if (isa<ReturnInst>(TI)) {
        Builder.setInsertionPoint(TI);
        Builder.createReleaseValue(Loc, SILValue(NewClosure),
                                   Builder.getDefaultAtomicity());
        continue;
      }

      // We use casts where findAllNonFailureExitBBs should have made sure that
      // this is true. This will ensure that the code is updated when we hit the
      // cast failure in debug builds.
      auto *Unreachable = cast<UnreachableInst>(TI);
      auto PrevIter = std::prev(SILBasicBlock::iterator(Unreachable));
      auto NoReturnApply = FullApplySite::isa(&*PrevIter);

      // We insert the release value right before the no return apply so that if
      // the partial apply is passed into the no-return function as an @owned
      // value, we will retain the partial apply before we release it and
      // potentially eliminate it.
      Builder.setInsertionPoint(NoReturnApply.getInstruction());
      Builder.createReleaseValue(Loc, SILValue(NewClosure), Builder.getDefaultAtomicity());
    }
  }
}

//===----------------------------------------------------------------------===//
//                            Closure Specializer
//===----------------------------------------------------------------------===//

namespace {

class ClosureSpecializer {

  /// A vector consisting of closures that we propagated. After
  std::vector<SILInstruction *> PropagatedClosures;
  bool IsPropagatedClosuresUniqued = false;

public:
  ClosureSpecializer() = default;

  void gatherCallSites(SILFunction *Caller,
                       llvm::SmallVectorImpl<ClosureInfo*> &ClosureCandidates,
                       llvm::DenseSet<FullApplySite> &MultipleClosureAI);
  bool specialize(SILFunction *Caller, SILFunctionTransform *SFT);

  ArrayRef<SILInstruction *> getPropagatedClosures() {
    if (IsPropagatedClosuresUniqued)
      return PropagatedClosures;

    sortUnique(PropagatedClosures);
    IsPropagatedClosuresUniqued = true;

    return PropagatedClosures;
  }
};

} // end anonymous namespace

void ClosureSpecializer::gatherCallSites(
    SILFunction *Caller,
    llvm::SmallVectorImpl<ClosureInfo*> &ClosureCandidates,
    llvm::DenseSet<FullApplySite> &MultipleClosureAI) {

  // A set of apply inst that we have associated with a closure. We use this to
  // make sure that we do not handle call sites with multiple closure arguments.
  llvm::DenseSet<FullApplySite> VisitedAI;

  // For each basic block BB in Caller...
  for (auto &BB : *Caller) {

    // For each instruction II in BB...
    for (auto &II : BB) {
      // If II is not a closure that we support specializing, skip it...
      if (!isSupportedClosure(&II))
        continue;

      ClosureInfo *CInfo = nullptr;

      // Go through all uses of our closure.
      for (auto *Use : II.getUses()) {
        // If this use is not an apply, there is nothing interesting for us to do,
        // so continue...
        auto AI = FullApplySite::isa(Use->getUser());
        if (!AI)
          continue;
        bool GenericClosure = AI.hasSubstitutions();
        if (!SupportGenericClosureSpecialization && AI.hasSubstitutions()) {
          //continue;
        }
        // Check if we have already associated this apply inst with a closure to
        // be specialized. We do not handle applies that take in multiple
        // closures at this time.
        if (!GenericClosure && !VisitedAI.insert(AI).second) {
          MultipleClosureAI.insert(AI);
          continue;
        }

        // If AI does not have a function_ref definition as its callee, we can
        // not do anything here... so continue...
        SILFunction *ApplyCallee = AI.getReferencedFunction();
        if (!ApplyCallee || ApplyCallee->isExternalDeclaration())
          continue;

        // Don't specialize non-fragile callees if the caller is fragile;
        // the specialized callee will have shared linkage, and thus cannot
        // be referenced from the fragile caller.
        if (Caller->isFragile() &&
            !ApplyCallee->hasValidLinkageForFragileInline())
          continue;

        // Ok, we know that we can perform the optimization but not whether or
        // not the optimization is profitable. Find the index of the argument
        // corresponding to our partial apply.
        Optional<unsigned> ClosureIndex;
        for (unsigned i = 0, e = AI.getNumArguments(); i != e; ++i) {
          if (AI.getArgument(i) != SILValue(&II))
            continue;
          ClosureIndex = i;
          DEBUG(llvm::dbgs() << "    Found callsite with closure argument at "
                << i << ": " << *AI.getInstruction());
          break;
        }

        // If we did not find an index, there is nothing further to do,
        // continue.
        if (!ClosureIndex.hasValue())
          continue;

        // Make sure that the Closure is invoked in the Apply's callee. We only
        // want to perform closure specialization if we know that we will be
        // able to change a partial_apply into an apply.
        //
        // TODO: Maybe just call the function directly instead of moving the
        // partial apply?
        SILValue Arg = ApplyCallee->getArgument(ClosureIndex.getValue());
        if (std::none_of(Arg->use_begin(), Arg->use_end(),
                         [&Arg](Operand *Op) -> bool {
                           auto UserAI = FullApplySite::isa(Op->getUser());
                           return UserAI && UserAI.getCallee() == Arg;
                         })) {
          continue;
        }

        unsigned firstParamArgIdx =
            AI.getSubstCalleeConv().getSILArgIndexOfFirstParam();
        assert(ClosureIndex.getValue() >= firstParamArgIdx);
        auto ClosureParamIndex = ClosureIndex.getValue() - firstParamArgIdx;

        auto ParamInfo = AI.getSubstCalleeType()->getParameters();
        SILParameterInfo ClosureParamInfo = ParamInfo[ClosureParamIndex];

        // Get all non-failure exit BBs in the Apply Callee if our partial apply
        // is guaranteed. If we do not understand one of the exit BBs, bail.
        //
        // We need this to make sure that we insert a release in the appropriate
        // locations to balance the +1 from the creation of the partial apply.
        llvm::TinyPtrVector<SILBasicBlock *> NonFailureExitBBs;
        if (ClosureParamInfo.isGuaranteed() &&
            !findAllNonFailureExitBBs(ApplyCallee, NonFailureExitBBs)) {
          continue;
        }

        if (!GenericClosure) {
          llvm::dbgs() << "ClosureSpecializer: found a non-generic closure\n";
          AI.getInstruction()->dumpInContext();
        }

        if (GenericClosure) {
          llvm::dbgs() << "ClosureSpecializer: found a generic closure\n";
          if (hasArchetypes(AI.getSubstitutions()))
            llvm::dbgs() << "Partial specialization is required\n";
          else
            llvm::dbgs() << "Full specialization is required\n";
          AI.getInstruction()->dumpInContext();
        }

        if (GenericClosure && !SupportGenericClosureSpecialization)
          continue;

        // Compute the final release points of the closure. We will insert
        // release of the captured arguments here.
        if (!CInfo) {
          CInfo = new ClosureInfo(&II);
          ValueLifetimeAnalysis VLA(CInfo->Closure);
          VLA.computeFrontier(CInfo->LifetimeFrontier,
                              ValueLifetimeAnalysis::AllowToModifyCFG);
        }

        // Now we know that CSDesc is profitable to specialize. Add it to our
        // call site list.
        CInfo->CallSites.push_back(
          CallSiteDescriptor(CInfo, AI, ClosureIndex.getValue(),
                             ClosureParamInfo, std::move(NonFailureExitBBs)));
      }
      if (CInfo)
        ClosureCandidates.push_back(CInfo);
    }
  }
}

bool ClosureSpecializer::specialize(SILFunction *Caller,
                                    SILFunctionTransform *SFT) {
  DEBUG(llvm::dbgs() << "Optimizing callsites that take closure argument in "
                     << Caller->getName() << '\n');

  // Collect all of the PartialApplyInsts that are used as arguments to
  // ApplyInsts. Check the profitability of specializing the closure argument.
  llvm::SmallVector<ClosureInfo*, 8> ClosureCandidates;
  llvm::DenseSet<FullApplySite> MultipleClosureAI;
  gatherCallSites(Caller, ClosureCandidates, MultipleClosureAI);

  bool Changed = false;
  for (auto *CInfo : ClosureCandidates) {
    for (auto &CSDesc : CInfo->CallSites) {
      // Do not specialize apply insts that take in multiple closures. This pass
      // does not know how to do this yet.
      if (MultipleClosureAI.count(CSDesc.getApplyInst()))
        continue;

      auto NewFName = CSDesc.createName();
      DEBUG(llvm::dbgs() << "    Perform optimizations with new name "
                         << NewFName << '\n');

      // Then see if we already have a specialized version of this function in
      // our module.
      SILFunction *NewF = CInfo->Closure->getModule().lookUpFunction(NewFName);

      // If not, create a specialized version of ApplyCallee calling the closure
      // directly.
      if (!NewF) {
        NewF = ClosureSpecCloner::cloneFunction(CSDesc, NewFName);
        SFT->notifyPassManagerOfFunction(NewF, CSDesc.getApplyCallee());
      }

      // Rewrite the call
      rewriteApplyInst(CSDesc, NewF);

      PropagatedClosures.push_back(CSDesc.getClosure());
      Changed = true;
    }
    delete CInfo;
  }
  return Changed;
}

//===----------------------------------------------------------------------===//
//                               Top Level Code
//===----------------------------------------------------------------------===//

namespace {

class SILClosureSpecializerTransform : public SILFunctionTransform {
public:
  SILClosureSpecializerTransform() {}

  void run() override {
    SILFunction *F = getFunction();

    // Don't optimize functions that are marked with the opt.never
    // attribute.
    if (!F->shouldOptimize())
      return;

    // If F is an external declaration, there is nothing to specialize.
    if (F->isExternalDeclaration())
      return;

    ClosureSpecializer C;
    if (!C.specialize(F, this))
      return;

    // If for testing purposes we were asked to not eliminate dead closures,
    // return.
    if (EliminateDeadClosures) {
      // Otherwise, remove any local dead closures that are now dead since we
      // specialized all of their uses.
      DEBUG(llvm::dbgs() << "Trying to remove dead closures!\n");
      for (SILInstruction *Closure : C.getPropagatedClosures()) {
        DEBUG(llvm::dbgs() << "    Visiting: " << *Closure);
        if (!tryDeleteDeadClosure(Closure)) {
          DEBUG(llvm::dbgs() << "        Failed to delete closure!\n");
          NumPropagatedClosuresNotEliminated++;
          continue;
        }

        DEBUG(llvm::dbgs() << "        Deleted closure!\n");
        ++NumPropagatedClosuresEliminated;
      }
    }

    // Invalidate everything since we delete calls as well as add new
    // calls and branches.
    invalidateAnalysis(SILAnalysis::InvalidationKind::Everything);
  }

  StringRef getName() override { return "Closure Specialization"; }
};

} // end anonymous namespace


SILTransform *swift::createClosureSpecializer() {
  return new SILClosureSpecializerTransform();
}
