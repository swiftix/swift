//===--- Generics.cpp ---- Utilities for transforming generics ------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2016 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "generic-specializer"

#include "swift/Strings.h"
#include "swift/SILOptimizer/Utils/Generics.h"
#include "swift/SILOptimizer/Utils/GenericCloner.h"
#include "swift/SILOptimizer/Utils/SpecializationMangler.h"
#include "swift/SIL/DebugUtils.h"
#include "swift/AST/GenericEnvironment.h"

using namespace swift;

// Max depth of a bound generic which can be processed by the generic
// specializer.
// E.g. the depth of Array<Array<Array<T>>> is 3.
// No specializations will be produced, if any of generic parameters contains
// a bound generic type with the depth higher than this threshold 
static const unsigned BoundGenericDepthThreshold = 50;

static unsigned getBoundGenericDepth(Type t) {
  unsigned Depth = 0;
  if (auto BGT = t->getAs<BoundGenericType>()) {
    Depth++;
    auto GenericArgs = BGT->getGenericArgs();
    unsigned MaxGenericArgDepth = 0;
    for (auto GenericArg : GenericArgs) {
      auto ArgDepth = getBoundGenericDepth(GenericArg);
      if (ArgDepth > MaxGenericArgDepth)
        MaxGenericArgDepth = ArgDepth;
    }
    Depth += MaxGenericArgDepth;
  }
  return Depth;
}

// =============================================================================
// ReabstractionInfo
// =============================================================================

/// Copy an entry from one substitution map into the other substitution map.
void copySubstitutionMapEntry(Type Ty, SubstitutionMap &From, SubstitutionMap &To) {
  auto CanTy = Ty->getCanonicalType();
  auto SubstTy = From.getMap().lookup(CanTy.getPointer());
  To.addSubstitution(CanTy, SubstTy);
  auto Parents = From.getParentMap().lookup(CanTy.getPointer());
  for (auto &Parent : Parents) {
    To.addParent(CanTy, Parent.first, Parent.second);
  }
  auto Conformances = From.getConformances(CanTy);
  if (!Conformances.empty())
    To.addConformances(CanTy, Conformances);
}

// Initialize SpecializedType iff the specialization is allowed.
ReabstractionInfo::ReabstractionInfo(SILFunction *OrigF,
                                     ArrayRef<Substitution> ParamSubs) {
  if (!OrigF->shouldOptimize()) {
    DEBUG(llvm::dbgs() << "    Cannot specialize function " << OrigF->getName()
                       << " marked to be excluded from optimizations.\n");
    return;
  }
  SpecializedGenericEnv = nullptr;
  OriginalParamSubs = ParamSubs;
  CallerParamSubs = ParamSubs;
  ClonerParamSubs = ParamSubs;

  SILModule &M = OrigF->getModule();
  Module *SM = M.getSwiftModule();

  SubstitutionMap InterfaceSubs;

  // Get the original substitution map.
  if (OrigF->getLoweredFunctionType()->getGenericSignature())
    InterfaceSubs = OrigF->getLoweredFunctionType()->getGenericSignature()
      ->getSubstitutionMap(ParamSubs);

  // Perform some checks to see if we need to bail.
  if (hasDynamicSelfTypes(InterfaceSubs.getMap())) {
    DEBUG(llvm::dbgs() << "    Cannot specialize with dynamic self.\n");
    return;
  }

  // Check if the substitution contains any generic types that are too deep.
  // If this is the case, bail to avoid the explosion in the number of 
  // generated specializations.
  for (auto Sub : ParamSubs) {
    auto Replacement = Sub.getReplacement();
    if (Replacement.findIf([](Type ty) -> bool {
          return getBoundGenericDepth(ty) >= BoundGenericDepthThreshold;
        })) {
      DEBUG(llvm::dbgs()
            << "    Cannot specialize because the generic type is too deep.\n");
      return;
    }
  }

  // Check if we have substitutions which replace generic type parameters with
  // concrete types or unbound generic types.
  bool HasConcreteGenericParams = false;
  bool HasUnboundGenericParams = false;
  for (auto &entry : InterfaceSubs.getMap()) {
    // Check only the substitutions for the generic parameters.
    // Ignore any dependent types, etc.
    if (!isa<GenericTypeParamType>(entry.first))
      continue;
    if (entry.second->getCanonicalType()->hasArchetype()) {
      HasUnboundGenericParams = true;
      continue;
    }
    HasConcreteGenericParams = true;
  }

  if (!HasConcreteGenericParams) {
    // All substititions are unbound.
    DEBUG(llvm::dbgs() <<
          "    Cannot specialize with all unbound interface substitutions.\n");
    DEBUG(for (auto Sub : ParamSubs) {
            Sub.dump();
          });
    return;
  }

  // We need a generic environment for the partial specialization.
  if (HasUnboundGenericParams && !OrigF->getGenericEnvironment())
    return;

  // Substitutions to be used to create a new function type for the
  // specialized function. If the the original substitution list mapped
  // a given generic parameter to a concrete type, then do the same.
  // Map all other generic parameters to themselves.
  SubstitutionMap CallerInterfaceSubs;
  if (!HasUnboundGenericParams)
    CallerInterfaceSubs = InterfaceSubs;

  if (HasUnboundGenericParams) {
    auto OrigGenSig = OrigF->getLoweredFunctionType()->getGenericSignature();
    auto OrigGenericEnv = OrigF->getGenericEnvironment();
    SpecializedGenSig = OrigGenSig;

    // Form a new generic signature based on the old one.
    ArchetypeBuilder Builder(*SM, M.getASTContext().Diags);

    // First, add the old generic signature.
    Builder.addGenericSignature(OrigGenSig, nullptr);

    // Checks if a given generic parameter type or a dependent type
    // is mapped to a non-concrete type, i.e. a type that has
    // archetypes. For dependent types, it also checks that its
    // base generic parameter type is also mapped to a non-concrete type.
    auto IsNonConcreteReplacementType =
        [&InterfaceSubs](CanType Ty, Type DefaultReplacementTy) -> bool {
      if (DefaultReplacementTy->getCanonicalType()->hasArchetype())
        return true;
      auto BaseTy = Ty;
      while (auto DepTy = dyn_cast<DependentMemberType>(BaseTy)) {
        BaseTy = DepTy->getBase()->getCanonicalType();
      };
      assert(isa<GenericTypeParamType>(BaseTy));
      return InterfaceSubs.getMap()
          .lookup(BaseTy.getPointer())
          ->getCanonicalType()
          ->hasArchetype();
    };

    // For each substitution with a concrete type as a replacement,
    // add a new concrete type equality requirement.
    for (auto &entry : InterfaceSubs.getMap()) {
      auto CanTy = entry.first->getCanonicalType();
      auto IsNonConcreteReplacement =
          IsNonConcreteReplacementType(CanTy, entry.second);
      if (!IsNonConcreteReplacement) {
        auto CanTy = entry.first->getCanonicalType();
        auto OutTy = CanTy;

        // TODO: For pre-specializations we need to add a different kind of a
        // requirement, e.g. that the type conforms to TrivialTypeOfSizeN or
        // to RefCountedObject.
        Builder.addSameTypeRequirementToConcrete(
            Builder.resolveArchetype(OutTy), entry.second->getCanonicalType(),
            RequirementSource(RequirementSource::Explicit, SourceLoc()));
      }
    }

    // Remember the new generic signature.
    SpecializedGenSig = Builder.getGenericSignature()->getCanonicalSignature();
    // Remember the new generic environment.
    SpecializedGenericEnv = Builder.getGenericEnvironment();

    // Substitution map to be used by the cloner.
    SubstitutionMap ClonerSubsMap;

    auto &InterfaceSubsMap = InterfaceSubs.getMap();
    auto &InterfaceParentMap = InterfaceSubs.getParentMap();
    auto ForwardingSubs = SpecializedGenericEnv->getForwardingSubstitutions(
        SM, SpecializedGenSig);
    auto ForwardingInterfaceSubsMap =
        SpecializedGenSig->getSubstitutionMap(ForwardingSubs);

    // Create new substitution maps. Simply copy the mappings for those types
    // which are mapped to concrete types in the original list of substitutions.
    // And if a generic parameter is mapped to a non-concrete type in the original
    // substitutions, simply map it to a corresponding archetype, i.e. do the
    // same what a forwarding substitution does.
    for (auto &entry : InterfaceSubsMap) {
      auto CanTy = entry.first->getCanonicalType();
      auto IsNonConcreteReplacement =
          IsNonConcreteReplacementType(CanTy, entry.second);
      if (IsNonConcreteReplacement) {
        Type Ty;

        // Map generic parameter type to an interface type in the
        // old generic environment.
        Ty = OrigGenericEnv->mapTypeOutOfContext(SM, CanTy)->getCanonicalType();
        CallerInterfaceSubs.addSubstitution(CanTy, Ty);

        // Map generic parameter type to a contextual type in the
        // new generic environment. This will be used by the cloner.
        Ty = SpecializedGenericEnv->mapTypeIntoContext(SM, CanTy)->getCanonicalType();
        ClonerSubsMap.addSubstitution(CanTy, Ty);

        // Copy conformances.

        // Conformances used for this generic parameter on the caller side.
        auto CallerSideConformances = InterfaceSubs.getConformances(CanTy);
        CallerInterfaceSubs.addConformances(CanTy, CallerSideConformances);

        // Conformances used for this generic parameter inside the callee, i.e.
        // inside specialization. They should be the same as for forwarding
        // substitutions.
        auto CalleeSideConformances =
            ForwardingInterfaceSubsMap.getConformances(CanTy);

        ClonerSubsMap.addConformances(CanTy, CalleeSideConformances);

        // Copy parents.
        auto Parents = InterfaceParentMap.lookup(CanTy.getPointer());
        for (auto &Parent : Parents) {
          CallerInterfaceSubs.addParent(CanTy, Parent.first, Parent.second);
          ClonerSubsMap.addParent(CanTy, Parent.first, Parent.second);
        }
      } else {
        // Copy entries if a replacement is a concrete type.
        copySubstitutionMapEntry(CanTy, InterfaceSubs, CallerInterfaceSubs);
        copySubstitutionMapEntry(CanTy, InterfaceSubs, ClonerSubsMap);
      }
    }

    // Create new substitutions lists for the caller and for the cloner.
    SmallVector<Substitution, 8> ClonerSubsVector;
    SmallVector<Substitution, 8> CallerSubsVector;

    // First, get a substitution map from the original signature.
    // It is based on the substitution list from the apply site.
    auto ParamMap = OrigGenSig->getSubstitutionMap(ParamSubs);
    // Then, use this map to form a list of substitutions for calling the
    // specialized function.
    // This new substitution list may contain less elements than the original one,
    // because generic parameter types with concrete type equality requirements
    // do not need a substitution.
    SpecializedGenSig->getSubstitutions(*SM, ParamMap, CallerSubsVector);

    // Form a substitution list to be used by the cloner when it clones the
    // body of the original function.
    OrigGenSig->getSubstitutions(*SM, ClonerSubsMap, ClonerSubsVector);

    auto &Ctx = M.getASTContext();
    CallerParamSubs = Ctx.AllocateCopy(CallerSubsVector);
    ClonerParamSubs = Ctx.AllocateCopy(ClonerSubsVector);
  }

  if (!HasUnboundGenericParams)
    SpecializedGenSig = nullptr;

  // Find out how the function type looks like after applying the provided
  // substitutions.
  SubstitutedType = createSubstitutedType(OrigF, CallerInterfaceSubs.getMap(),
                                          HasUnboundGenericParams);
  assert(!SubstitutedType->hasArchetype() &&
         "Substituted function type should not contain archetypes");

  // Check which parameters and results can be converted from
  // indirect to direct ones.
  NumResults = SubstitutedType->getNumIndirectResults();
  Conversions.resize(NumResults + SubstitutedType->getParameters().size());

  if (SubstitutedType->getNumDirectResults() == 0) {
    // The original function has no direct result yet. Try to convert the first
    // indirect result to a direct result.
    // TODO: We could also convert multiple indirect results by returning a
    // tuple type and created tuple_extract instructions at the call site.
    unsigned IdxForResult = 0;
    for (SILResultInfo RI : SubstitutedType->getIndirectResults()) {
      assert(RI.isIndirect());
      if (!RI.getSILType().hasTypeParameter() &&
          RI.getSILType().isLoadable(M) && !RI.getType()->isVoid()) {
        Conversions.set(IdxForResult);
        break;
      }
      ++IdxForResult;
    }
  }

  // Try to convert indirect incoming parameters to direct parameters.
  unsigned IdxForParam = NumResults;
  for (SILParameterInfo PI : SubstitutedType->getParameters()) {
    if (!PI.getSILType().hasTypeParameter() &&
        PI.getSILType().isLoadable(M) &&
        PI.getConvention() == ParameterConvention::Indirect_In) {
      Conversions.set(IdxForParam);
    }
    ++IdxForParam;
  }

  // Produce a specialized type, which is the substituted type with
  // the parameters/results passing conventions adjusted according
  // to the converions selected above.
  SpecializedType = createSpecializedType(SubstitutedType, M);
}

/// Create a new substituted type with the updated signature.
CanSILFunctionType
ReabstractionInfo::createSubstitutedType(SILFunction *OrigF,
                                         const TypeSubstitutionMap &SubstMap,
                                         bool HasUnboundGenericParams) {
  auto &M = OrigF->getModule();
  auto SM = M.getSwiftModule();
  auto OrigFnTy = OrigF->getLoweredFunctionType();

  // First substitute concrete types into the existing function type.
  auto FnTy = SILType::substFuncType(M, SM, SubstMap, OrigFnTy,
                                     /*dropGenerics = */ true);
  if (!HasUnboundGenericParams)
    return FnTy;

  // Use the new specialized generic signature.
  auto NewFnTy = SILFunctionType::get(
      SpecializedGenSig, FnTy->getExtInfo(), FnTy->getCalleeConvention(),
      FnTy->getParameters(), FnTy->getAllResults(),
      FnTy->getOptionalErrorResult(), M.getASTContext());

  // This is an interface type. It should not have any type parameters or
  // archetypes.
  assert(!NewFnTy->hasTypeParameter() && !NewFnTy->hasArchetype());
  return NewFnTy;
}

// Convert the substituted function type into a specialized function type based
// on the ReabstractionInfo.
CanSILFunctionType ReabstractionInfo::
createSpecializedType(CanSILFunctionType SubstFTy, SILModule &M) const {
  llvm::SmallVector<SILResultInfo, 8> SpecializedResults;
  llvm::SmallVector<SILParameterInfo, 8> SpecializedParams;

  unsigned ResultIdx = 0;
  for (SILResultInfo RI : SubstFTy->getAllResults()) {
    if (RI.isDirect()) {
      SpecializedResults.push_back(RI);
    } else {
      if (isResultConverted(ResultIdx++)) {
        // Convert the indirect result to a direct result.
        SILType SILResTy = SILType::getPrimitiveObjectType(RI.getType());
        // Indirect results are passed as owned, so we also need to pass the
        // direct result as owned (except it's a trivial type).
        auto C = (SILResTy.isTrivial(M) ? ResultConvention::Unowned :
                  ResultConvention::Owned);
        SpecializedResults.push_back(SILResultInfo(RI.getType(), C));
      } else {
        // No conversion: re-use the original result info.
        SpecializedResults.push_back(RI);
      }
    }
  }
  unsigned ParamIdx = 0;
  for (SILParameterInfo PI : SubstFTy->getParameters()) {
    if (isParamConverted(ParamIdx++)) {
      // Convert the indirect parameter to a direct parameter.
      SILType SILParamTy = SILType::getPrimitiveObjectType(PI.getType());
      // Indirect parameters are passed as owned, so we also need to pass the
      // direct parameter as owned (except it's a trivial type).
      auto C = ((!SILParamTy.hasTypeParameter() && SILParamTy.isTrivial(M))
                    ? ParameterConvention::Direct_Unowned
                    : ParameterConvention::Direct_Owned);
      SpecializedParams.push_back(SILParameterInfo(PI.getType(), C));
    } else {
      // No conversion: re-use the original parameter info.
      SpecializedParams.push_back(PI);
    }
  }
  return
    SILFunctionType::get(SubstFTy->getGenericSignature(),
                         SubstFTy->getExtInfo(),
                         SubstFTy->getCalleeConvention(), SpecializedParams,
                         SpecializedResults, SubstFTy->getOptionalErrorResult(),
                         M.getASTContext());
}

// =============================================================================
// GenericFuncSpecializer
// =============================================================================

GenericFuncSpecializer::GenericFuncSpecializer(SILFunction *GenericFunc,
                                               ArrayRef<Substitution> ParamSubs,
                                               IsFragile_t Fragile,
                                               const ReabstractionInfo &ReInfo)
    : M(GenericFunc->getModule()),
      GenericFunc(GenericFunc),
      ParamSubs(ParamSubs),
      Fragile(Fragile),
      ReInfo(ReInfo) {

  assert(GenericFunc->isDefinition() && "Expected definition to specialize!");

  //auto FnTy = ReInfo.getSubstitutedType();
  auto FnTy = ReInfo.getSpecializedType();
  Mangle::Mangler Mangler;

  // TODO: Use the SILFunctionType of the substituted function type for the mangling.
  // Encode this whole type. What would be the name length increase? Do we need to
  // go for a shorter way of encoding the type/substitutionss?
  // If we go for encoding the SILFunctionType, we don't need the
  // AdjustedParamSubstitutions anymore, because the SILFunctionType type would contain
  // all we need in form of equal type constraints.
  GenericSpecializationMangler OldGenericMangler(Mangler, GenericFunc, FnTy,
                                                 Fragile);
  OldGenericMangler.mangle();
  std::string Old = Mangler.finalize();

  NewMangling::GenericSpecializationMangler NewGenericMangler(
      GenericFunc, FnTy, Fragile, /*isReAbstracted*/ true);
  std::string New = NewGenericMangler.mangle();
  ClonedName = NewMangling::selectMangling(Old, New);

  DEBUG(llvm::dbgs() << "    Specialized function " << ClonedName << '\n');
}

// Return an existing specialization if one exists.
SILFunction *GenericFuncSpecializer::lookupSpecialization() {
  if (SILFunction *SpecializedF = M.lookUpFunction(ClonedName)) {
    assert(ReInfo.getSpecializedType()
           == SpecializedF->getLoweredFunctionType() &&
           "Previously specialized function does not match expected type.");
    DEBUG(llvm::dbgs() << "Found an existing specialization for: " << ClonedName
                       << "\n");
    return SpecializedF;
  }
  DEBUG(llvm::dbgs() << "Could not find an existing specialization for: "
                     << ClonedName << "\n");
  return nullptr;
}

// Forward decl for prespecialization support.
static bool linkSpecialization(SILModule &M, SILFunction *F);

// Create a new specialized function if possible, and cache it.
SILFunction *GenericFuncSpecializer::tryCreateSpecialization() {
  // Do not create any new specializations at Onone.
  if (M.getOptions().Optimization <= SILOptions::SILOptMode::None)
    return nullptr;

  DEBUG(
    if (M.getOptions().Optimization <= SILOptions::SILOptMode::Debug) {
      llvm::dbgs() << "Creating a specialization: " << ClonedName << "\n"; });

  // Create a new function.
  SILFunction *SpecializedF = GenericCloner::cloneFunction(
      GenericFunc, Fragile, ReInfo,
      // Use these substitutions inside the new specialized function being
      // created.
      ReInfo.getClonerParamSubstitutions(),
      ClonedName);
  assert(SpecializedF->hasUnqualifiedOwnership());
  // Check if this specialization should be linked for prespecialization.
  linkSpecialization(M, SpecializedF);
  return SpecializedF;
}

// =============================================================================
// Apply substitution
// =============================================================================

/// Fix the case where a void function returns the result of an apply, which is
/// also a call of a void-returning function.
/// We always want a void function returning a tuple _instruction_.
static void fixUsedVoidType(SILValue VoidVal, SILLocation Loc,
                            SILBuilder &Builder) {
  assert(VoidVal->getType().isVoid());
  if (VoidVal->use_empty())
    return;
  auto *NewVoidVal = Builder.createTuple(Loc, VoidVal->getType(), { });
  VoidVal->replaceAllUsesWith(NewVoidVal);
}

// Create a new apply based on an old one, but with a different
// function being applied.
static ApplySite replaceWithSpecializedCallee(ApplySite AI,
                                              SILValue Callee,
                                              SILBuilder &Builder,
                                              const ReabstractionInfo &ReInfo) {
  SILLocation Loc = AI.getLoc();
  SmallVector<SILValue, 4> Arguments;
  SILValue StoreResultTo;
  unsigned Idx = ReInfo.getIndexOfFirstArg(AI);
  for (auto &Op : AI.getArgumentOperands()) {
    if (ReInfo.isArgConverted(Idx)) {
      if (ReInfo.isResultIndex(Idx)) {
        // The result is converted from indirect to direct. We need to insert
        // a store later.
        assert(!StoreResultTo);
        StoreResultTo = Op.get();
      } else {
        // An argument is converted from indirect to direct. Instead of the
        // address we pass the loaded value.
        SILValue Val = Builder.createLoad(Loc, Op.get(),
                                          LoadOwnershipQualifier::Unqualified);
        Arguments.push_back(Val);
      }
    } else {
      Arguments.push_back(Op.get());
    }
    ++Idx;
  }

  // Create a substituted callee type.
  auto CanFnTy = dyn_cast<SILFunctionType>(
      Callee->getType().getSwiftRValueType()->getCanonicalType());
  auto CalleeSubstFnTy = CanFnTy;
  assert(CanFnTy == ReInfo.getSpecializedType() && "Types should be the same");

  ArrayRef<Substitution> Subs;
  if (ReInfo.getSpecializedType()->isPolymorphic()) {
    Subs = ReInfo.getCallerParamSubstitutions();
    CalleeSubstFnTy = CanFnTy->substGenericArgs(
        AI.getModule(), AI.getModule().getSwiftModule(),
        ReInfo.getCallerParamSubstitutions());
    assert(!CalleeSubstFnTy->isPolymorphic() &&
           "Substituted callee type should not be polymorphic");
    assert(!CalleeSubstFnTy->hasTypeParameter() &&
           "Substituted callee type should not have type parameters");
  }

  auto CalleeSILSubstFnTy = SILType::getPrimitiveObjectType(CalleeSubstFnTy);

  if (auto *TAI = dyn_cast<TryApplyInst>(AI)) {
    SILBasicBlock *ResultBB = TAI->getNormalBB();
    assert(ResultBB->getSinglePredecessorBlock() == TAI->getParent());
    auto *NewTAI =
        Builder.createTryApply(Loc, Callee, CalleeSILSubstFnTy, Subs, Arguments,
                               ResultBB, TAI->getErrorBB());
    if (StoreResultTo) {
      // The original normal result of the try_apply is an empty tuple.
      assert(ResultBB->getNumArguments() == 1);
      Builder.setInsertionPoint(ResultBB->begin());
      fixUsedVoidType(ResultBB->getArgument(0), Loc, Builder);

      SILArgument *Arg = ResultBB->replaceArgument(
          0, StoreResultTo->getType().getObjectType());
      // Store the direct result to the original result address.
      Builder.createStore(Loc, Arg, StoreResultTo,
                          StoreOwnershipQualifier::Unqualified);
    }
    return NewTAI;
  }
  if (auto *A = dyn_cast<ApplyInst>(AI)) {
    auto *NewAI = Builder.createApply(Loc, Callee, CalleeSILSubstFnTy,
                                      CalleeSubstFnTy->getSILResult(), Subs,
                                      Arguments, A->isNonThrowing());
    if (StoreResultTo) {
      // Store the direct result to the original result address.
      fixUsedVoidType(A, Loc, Builder);
      Builder.createStore(Loc, NewAI, StoreResultTo,
                          StoreOwnershipQualifier::Unqualified);
    }
    A->replaceAllUsesWith(NewAI);
    return NewAI;
  }
  if (auto *PAI = dyn_cast<PartialApplyInst>(AI)) {
    CanSILFunctionType NewPAType = ReInfo.createSpecializedType(
        PAI->getFunctionType(), Builder.getModule());
    // SILType PTy =
    // SILType::getPrimitiveObjectType(ReInfo.getSpecializedType());
    SILType PTy = CalleeSILSubstFnTy;
    auto *NewPAI =
        Builder.createPartialApply(Loc, Callee, PTy, Subs, Arguments,
                                   SILType::getPrimitiveObjectType(NewPAType));
    PAI->replaceAllUsesWith(NewPAI);
    return NewPAI;
  }
  llvm_unreachable("unhandled kind of apply");
}

// Create a new apply based on an old one, but with a different
// function being applied.
ApplySite swift::
replaceWithSpecializedFunction(ApplySite AI, SILFunction *NewF,
                               const ReabstractionInfo &ReInfo) {
  SILBuilderWithScope Builder(AI.getInstruction());
  FunctionRefInst *FRI = Builder.createFunctionRef(AI.getLoc(), NewF);
  return replaceWithSpecializedCallee(AI, FRI, Builder, ReInfo);
}

/// Create a re-abstraction thunk for a partial_apply.
/// This is needed in case we converted some parameters/results of the
/// specialized function from indirect to direct but the result function of the
/// partial_apply still needs them as indirect.
/// We create a thunk which converts the direct parameters/results back to
/// indirect ones.
static SILFunction *createReabstractionThunk(const ReabstractionInfo &ReInfo,
                                     PartialApplyInst *OrigPAI,
                                     SILFunction *SpecializedFunc) {
  SILFunction *OrigF = OrigPAI->getCalleeFunction();
  SILModule &M = OrigF->getModule();

  IsFragile_t Fragile = IsNotFragile;
  if (OrigF->isFragile() && OrigPAI->getFunction()->isFragile())
    Fragile = IsFragile;

  std::string ThunkName;
  {
    Mangle::Mangler M;
    GenericSpecializationMangler OldMangler(
        M, OrigF, ReInfo.getSubstitutedType(), Fragile,
        GenericSpecializationMangler::NotReabstracted);
    OldMangler.mangle();
    std::string Old = M.finalize();

    NewMangling::GenericSpecializationMangler NewMangler(
        OrigF, ReInfo.getSubstitutedType(), Fragile,
        /*isReAbstracted*/ false);
    std::string New = NewMangler.mangle();
    ThunkName = NewMangling::selectMangling(Old, New);
  }

  auto Loc = RegularLocation::getAutoGeneratedLocation();

  SILFunction *Thunk = M.lookUpFunction(ThunkName);
  if (Thunk) {
    // Re-use an existing thunk.
    assert(Thunk->getLoweredFunctionType() == ReInfo.getSubstitutedType());
    assert(Thunk->getLinkage() == SILLinkage::Shared ||
           stripExternalFromLinkage(Thunk->getLinkage()) == SILLinkage::Shared);
    if (!Thunk->empty())
      return Thunk;
  }

  if (!Thunk) {
    Thunk = M.createFunction(
        SILLinkage::Shared, ThunkName, ReInfo.getSubstitutedType(),
        ReInfo.getSpecializedGenericEnvironment(), Loc, IsBare, IsTransparent,
        Fragile, IsThunk, SILFunction::NotRelevant);
    Thunk->setDebugScope(new (M) SILDebugScope(Loc, Thunk));
  }

  SILBasicBlock *EntryBB = Thunk->createBasicBlock();
  SILBuilder Builder(EntryBB);
  SILBasicBlock *SpecEntryBB = &*SpecializedFunc->begin();
  CanSILFunctionType SpecType = SpecializedFunc->getLoweredFunctionType();
  SILArgument *ReturnValueAddr = nullptr;

  // If the original specialized function had unqualified ownership, set the
  // thunk to have unqualified ownership as well.
  //
  // This is a stop gap measure to allow for easy inlining. We could always make
  // the Thunk qualified, but then we would need to either fix the inliner to
  // inline qualified into unqualified functions /or/ have the
  // OwnershipModelEliminator run as part of the normal compilation pipeline
  // (which we are not doing yet).
  if (SpecializedFunc->hasUnqualifiedOwnership()) {
    Thunk->setUnqualifiedOwnership();
  }

  // Convert indirect to direct parameters/results.
  SmallVector<SILValue, 4> Arguments;
  auto SpecArgIter = SpecEntryBB->args_begin();
  for (unsigned Idx = 0; Idx < ReInfo.getNumArguments(); Idx++) {
    if (ReInfo.isArgConverted(Idx)) {
      if (ReInfo.isResultIndex(Idx)) {
        // Store the result later.
        SILType Ty = SpecType->getSILResult().getAddressType();
        ReturnValueAddr = EntryBB->createArgument(Ty);
      } else {
        // Instead of passing the address, pass the loaded value.
        SILArgument *SpecArg = *SpecArgIter++;
        SILType Ty = SpecArg->getType().getAddressType();
        SILArgument *NewArg = EntryBB->createArgument(Ty, SpecArg->getDecl());
        auto *ArgVal = Builder.createLoad(Loc, NewArg,
                                          LoadOwnershipQualifier::Unqualified);
        Arguments.push_back(ArgVal);
      }
    } else {
      // No change to the argument.
      SILArgument *SpecArg = *SpecArgIter++;
      SILArgument *NewArg =
          EntryBB->createArgument(SpecArg->getType(), SpecArg->getDecl());
      Arguments.push_back(NewArg);
    }
  }

  auto *FRI = Builder.createFunctionRef(Loc, SpecializedFunc);
  ArrayRef<Substitution> Subs;
  if (ReInfo.getSpecializedType()->isPolymorphic()) {
    Subs = ReInfo.getCallerParamSubstitutions();
  }

  // Create a substituted callee type.
  auto CanFnTy = dyn_cast<SILFunctionType>(
      FRI->getType().getSwiftRValueType()->getCanonicalType());
  auto CalleeSubstFnTy = CanFnTy;

  if (!Subs.empty()) {
    CalleeSubstFnTy = CanFnTy->substGenericArgs(
        M, M.getSwiftModule(), ReInfo.getCallerParamSubstitutions());
  }
  auto FnTy = SILType::getPrimitiveObjectType(CalleeSubstFnTy);

  SILValue ReturnValue;
  if (SpecType->hasErrorResult()) {
    // Create the logic for calling a throwing function.
    SILBasicBlock *NormalBB = Thunk->createBasicBlock();
    SILBasicBlock *ErrorBB = Thunk->createBasicBlock();
    Builder.createTryApply(Loc, FRI, FnTy,
                           Subs, Arguments, NormalBB, ErrorBB);
    auto *ErrorVal =
        ErrorBB->createArgument(SpecType->getErrorResult().getSILType());
    Builder.setInsertionPoint(ErrorBB);
    Builder.createThrow(Loc, ErrorVal);
    ReturnValue = NormalBB->createArgument(SpecType->getSILResult());
    Builder.setInsertionPoint(NormalBB);
  } else {
    ReturnValue = Builder.createApply(Loc, FRI, FnTy,
                                      SpecType->getSILResult(), Subs,
                                      Arguments, false);
  }
  if (ReturnValueAddr) {
    // Need to store the direct results to the original indirect address.
    Builder.createStore(Loc, ReturnValue, ReturnValueAddr,
                        StoreOwnershipQualifier::Unqualified);
    SILType VoidTy = OrigPAI->getSubstCalleeType()->getSILResult();
    assert(VoidTy.isVoid());
    ReturnValue = Builder.createTuple(Loc, VoidTy, { });
  }
  Builder.createReturn(Loc, ReturnValue);

  return Thunk;
}

void swift::trySpecializeApplyOfGeneric(
    ApplySite Apply, DeadInstructionSet &DeadApplies,
    llvm::SmallVectorImpl<SILFunction *> &NewFunctions) {
  assert(Apply.hasSubstitutions() && "Expected an apply with substitutions!");

  auto *F = Apply.getInstruction()->getFunction();
  auto *RefF = cast<FunctionRefInst>(Apply.getCallee())->getReferencedFunction();

  DEBUG(llvm::dbgs() << "  ApplyInst:\n";
        Apply.getInstruction()->dumpInContext());

  // If the caller is fragile but the callee is not, bail out.
  // Specializations have shared linkage, which means they do
  // not have an external entry point, Since the callee is not
  // fragile we cannot serialize the body of the specialized
  // callee either.
  if (F->isFragile() && !RefF->hasValidLinkageForFragileInline())
      return;

  // If the caller and callee are both fragile, preserve the fragility when
  // cloning the callee. Otherwise, strip it off so that we can optimize
  // the body more.
  IsFragile_t Fragile = IsNotFragile;
  if (F->isFragile() && RefF->isFragile())
    Fragile = IsFragile;

  ReabstractionInfo ReInfo(RefF, Apply.getSubstitutions());
  if (!ReInfo.getSpecializedType())
    return;

  SILModule &M = F->getModule();

  bool needAdaptUsers = false;
  bool replacePartialApplyWithoutReabstraction = false;
  auto *PAI = dyn_cast<PartialApplyInst>(Apply);
  // TODO: Partial specializations of partial applies are
  // not supported yet.
  if (PAI && ReInfo.getSpecializedType()->isPolymorphic())
    return;
  if (PAI && ReInfo.hasConversions()) {
    // If we have a partial_apply and we converted some results/parameters from
    // indirect to direct there are 3 cases:
    // 1) All uses of the partial_apply are apply sites again. In this case
    //    we can just adapt all the apply sites which use the partial_apply.
    // 2) The result of the partial_apply is re-abstracted anyway (and the
    //    re-abstracted function type matches with our specialized type). In
    //    this case we can just skip the existing re-abstraction.
    // 3) For all other cases we need to create a new re-abstraction thunk.
    needAdaptUsers = true;
    for (Operand *Use : PAI->getUses()) {
      SILInstruction *User = Use->getUser();
      if (isa<RefCountingInst>(User))
        continue;
      if (isDebugInst(User))
        continue;

      auto FAS = FullApplySite::isa(User);
      if (FAS && FAS.getCallee() == Apply.getInstruction())
        continue;

      auto *PAIUser = dyn_cast<PartialApplyInst>(User);
      if (PAIUser && isPartialApplyOfReabstractionThunk(PAIUser)) {
        CanSILFunctionType NewPAType =
          ReInfo.createSpecializedType(PAI->getFunctionType(), M);
        if (PAIUser->getFunctionType() == NewPAType)
          continue;
      }
      replacePartialApplyWithoutReabstraction = true;
      break;
    }
  }

  GenericFuncSpecializer FuncSpecializer(RefF, Apply.getSubstitutions(),
                                         Fragile, ReInfo);
  SILFunction *SpecializedF = FuncSpecializer.lookupSpecialization();
  if (SpecializedF) {
    // Even if the pre-specialization exists already, try to preserve it
    // if it is whitelisted.
    linkSpecialization(M, SpecializedF);
  } else {
    SpecializedF = FuncSpecializer.tryCreateSpecialization();
    if (!SpecializedF)
      return;

    assert(SpecializedF->hasUnqualifiedOwnership());
    NewFunctions.push_back(SpecializedF);
  }

  assert(ReInfo.getSpecializedType()
         == SpecializedF->getLoweredFunctionType() &&
         "Previously specialized function does not match expected type.");

  // FIXME: Replace pre-specialization's "keep as public" hack with something
  // more principled
  assert((Fragile == SpecializedF->isFragile() ||
          SpecializedF->isKeepAsPublic()) &&
         "Previously specialized function does not match expected "
         "resilience level.");

  DeadApplies.insert(Apply.getInstruction());

  if (replacePartialApplyWithoutReabstraction) {
    // There are some unknown users of the partial_apply. Therefore we need a
    // thunk which converts from the re-abstracted function back to the
    // original function with indirect parameters/results.
    auto *PAI = cast<PartialApplyInst>(Apply.getInstruction());
    SILBuilderWithScope Builder(PAI);
    SILFunction *Thunk = createReabstractionThunk(ReInfo, PAI, SpecializedF);
    NewFunctions.push_back(Thunk);
    auto *FRI = Builder.createFunctionRef(PAI->getLoc(), Thunk);
    SmallVector<SILValue, 4> Arguments;
    for (auto &Op : PAI->getArgumentOperands()) {
      Arguments.push_back(Op.get());
    }
    auto *NewPAI = Builder.createPartialApply(PAI->getLoc(), FRI,
                                      PAI->getSubstCalleeSILType(),
                                      {},
                                      Arguments,
                                      PAI->getType());
    PAI->replaceAllUsesWith(NewPAI);
    DeadApplies.insert(PAI);
    return;
  }
  // Make the required changes to the call site.
  ApplySite newApply = replaceWithSpecializedFunction(Apply, SpecializedF,
                                                      ReInfo);
  if (needAdaptUsers) {
    // Adapt all known users of the partial_apply. This is needed in case we
    // converted some indirect parameters/results to direct ones.
    auto *NewPAI = cast<PartialApplyInst>(newApply);
    ReInfo.prunePartialApplyArgs(NewPAI->getNumArguments());
    for (Operand *Use : NewPAI->getUses()) {
      SILInstruction *User = Use->getUser();
      if (auto FAS = FullApplySite::isa(User)) {
        SILBuilder Builder(User);
        replaceWithSpecializedCallee(FAS, NewPAI, Builder, ReInfo);
        DeadApplies.insert(FAS.getInstruction());
        continue;
      }
      if (auto *PAI = dyn_cast<PartialApplyInst>(User)) {
        // This is a partial_apply of a re-abstraction thunk. Just skip this.
        assert(PAI->getType() == NewPAI->getType());
        PAI->replaceAllUsesWith(NewPAI);
        DeadApplies.insert(PAI);
      }
    }
  }
}

// =============================================================================
// Prespecialized symbol lookup.
//
// This uses the SIL linker to checks for the does not load the body of the pres
// =============================================================================

static void keepSpecializationAsPublic(SILFunction *F) {
  DEBUG(auto DemangledNameString =
            swift::Demangle::demangleSymbolAsString(F->getName());
        StringRef DemangledName = DemangledNameString;
        llvm::dbgs() << "Keep specialization public: " << DemangledName << " : "
                     << F->getName() << "\n");
  // Make it public, so that others can refer to it.
  //
  // NOTE: This function may refer to non-public symbols, which may lead to
  // problems, if you ever try to inline this function. Therefore, these
  // specializations should only be used to refer to them, but should never
  // be inlined!  The general rule could be: Never inline specializations
  // from stdlib!
  //
  // NOTE: Making these specializations public at this point breaks
  // some optimizations. Therefore, just mark the function.
  // DeadFunctionElimination pass will check if the function is marked
  // and preserve it if required.
  F->setKeepAsPublic(true);
}

/// Link a specialization for generating prespecialized code.
///
/// For now, it is performed only for specializations in the
/// standard library. But in the future, one could think of
/// maintaining a cache of optimized specializations.
///
/// Mark specializations as public, so that they can be used by user
/// applications. These specializations are generated during -O compilation of
/// the library, but only used only by client code compiled at -Onone. They
/// should be never inlined.
static bool linkSpecialization(SILModule &M, SILFunction *F) {
  if (F->isKeepAsPublic())
    return true;
  // Do not remove functions from the white-list. Keep them around.
  // Change their linkage to public, so that other applications can refer to it.
  if (M.getOptions().Optimization >= SILOptions::SILOptMode::Optimize &&
      F->getModule().getSwiftModule()->getName().str() == SWIFT_ONONE_SUPPORT) {
    if (isWhitelistedSpecialization(F->getName())) {
      keepSpecializationAsPublic(F);
      return true;
    }
  }
  return false;
}

// The whitelist of classes and functions from the stdlib,
// whose specializations we want to preserve.
static const char *const WhitelistedSpecializations[] = {
    "Array",
    "_ArrayBuffer",
    "_ContiguousArrayBuffer",
    "Range",
    "RangeIterator",
    "CountableRange",
    "CountableRangeIterator",
    "ClosedRange",
    "ClosedRangeIterator",
    "CountableClosedRange",
    "CountableClosedRangeIterator",
    "IndexingIterator",
    "Collection",
    "MutableCollection",
    "BidirectionalCollection",
    "RandomAccessCollection",
    "RangeReplaceableCollection",
    "_allocateUninitializedArray",
    "UTF8",
    "UTF16",
    "String",
    "_StringBuffer",
    "_toStringReadOnlyPrintable",
};

/// Check of a given name could be a name of a white-listed
/// specialization.
bool swift::isWhitelistedSpecialization(StringRef SpecName) {
  // TODO: Once there is an efficient API to check if
  // a given symbol is a specialization of a specific type,
  // use it instead. Doing demangling just for this check
  // is just wasteful.
  auto DemangledNameString =
     swift::Demangle::demangleSymbolAsString(SpecName);

  StringRef DemangledName = DemangledNameString;

  DEBUG(llvm::dbgs() << "Check if whitelisted: " << DemangledName << "\n");

  auto pos = DemangledName.find("generic ", 0);
  auto oldpos = pos;
  if (pos == StringRef::npos)
    return false;

  // Create "of Swift"
  llvm::SmallString<64> OfString;
  llvm::raw_svector_ostream buffer(OfString);
  buffer << "of ";
  buffer << STDLIB_NAME <<'.';

  StringRef OfStr = buffer.str();
  DEBUG(llvm::dbgs() << "Check substring: " << OfStr << "\n");

  pos = DemangledName.find(OfStr, oldpos);

  if (pos == StringRef::npos) {
    // Create "of (extension in Swift).Swift"
    llvm::SmallString<64> OfString;
    llvm::raw_svector_ostream buffer(OfString);
    buffer << "of (extension in " << STDLIB_NAME << "):";
    buffer << STDLIB_NAME << '.';
    OfStr = buffer.str();
    pos = DemangledName.find(OfStr, oldpos);
    DEBUG(llvm::dbgs() << "Check substring: " << OfStr << "\n");
    if (pos == StringRef::npos)
      return false;
  }

  pos += OfStr.size();

  for (auto NameStr: WhitelistedSpecializations) {
    StringRef Name = NameStr;
    auto pos1 = DemangledName.find(Name, pos);
    if (pos1 == pos && !isalpha(DemangledName[pos1+Name.size()])) {
      return true;
    }
  }

  return false;
}

/// Try to look up an existing specialization in the specialization cache.
/// If it is found, it tries to link this specialization.
///
/// For now, it performs a lookup only in the standard library.
/// But in the future, one could think of maintaining a cache
/// of optimized specializations.
static SILFunction *lookupExistingSpecialization(SILModule &M,
                                                 StringRef FunctionName) {
  // Try to link existing specialization only in -Onone mode.
  // All other compilation modes perform specialization themselves.
  // TODO: Cache optimized specializations and perform lookup here?
  // Only check that this function exists, but don't read
  // its body. It can save some compile-time.
  if (isWhitelistedSpecialization(FunctionName))
    return M.hasFunction(FunctionName, SILLinkage::PublicExternal);

  return nullptr;
}

SILFunction *swift::lookupPrespecializedSymbol(SILModule &M,
                                               StringRef FunctionName) {
  // First check if the module contains a required specialization already.
  auto *Specialization = M.lookUpFunction(FunctionName);
  if (Specialization) {
    if (Specialization->getLinkage() == SILLinkage::PublicExternal)
      return Specialization;
  }

  // Then check if the required specialization can be found elsewhere.
  Specialization = lookupExistingSpecialization(M, FunctionName);
  if (!Specialization)
    return nullptr;

  assert(hasPublicVisibility(Specialization->getLinkage()) &&
         "Pre-specializations should have public visibility");

  Specialization->setLinkage(SILLinkage::PublicExternal);

  assert(Specialization->isExternalDeclaration()  &&
         "Specialization should be a public external declaration");

  DEBUG(llvm::dbgs() << "Found existing specialization for: " << FunctionName
                     << '\n';
        llvm::dbgs() << swift::Demangle::demangleSymbolAsString(
                            Specialization->getName())
                     << "\n\n");

  return Specialization;
}
