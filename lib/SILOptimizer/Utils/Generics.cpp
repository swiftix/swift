//===--- Generics.cpp ---- Utilities for transforming generics ------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2016 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See http://swift.org/LICENSE.txt for license information
// See http://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "generic-specializer"

#include "swift/Strings.h"
#include "swift/SILOptimizer/Utils/Generics.h"
#include "swift/SILOptimizer/Utils/GenericCloner.h"
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

// Initialize SpecializedType iff the specialization is allowed.
ReabstractionInfo::ReabstractionInfo(SILFunction *OrigF,
                                     ArrayRef<Substitution> Subs) {
  if (!OrigF->shouldOptimize()) {
    DEBUG(llvm::dbgs() << "    Cannot specialize function " << OrigF->getName()
                       << " marked to be excluded from optimizations.\n");
    return;
  }
  SpecializedGenericEnv = nullptr;
  ParamSubs = Subs;
  SpecializedParamSubs = ParamSubs;
  AdjustedParamSubs = ParamSubs;
  AdjustedCloningParamSubs = ParamSubs;

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

  auto OrigGenSig = OrigF->getLoweredFunctionType()->getGenericSignature();
  auto OrigGenericEnv = OrigF->getGenericEnvironment();
  SpecializedGenSig = OrigGenSig;

  SubstitutionMap AdjustedCloningSubs = InterfaceSubs;
  // Adjusted substitution map for the caller, which maps
  // generic parameters to the contextual types. It is used
  // to create an adjusted set of substitutions for the
  // caller's apply instruction which will invoke the specialized
  // function.
  SubstitutionMap AdjustedParamSubsMap = InterfaceSubs;
  AdjustedInterfaceSubs = InterfaceSubs;

  if (HasUnboundGenericParams) {
    // Try to form a new generic signature based on the old one.
    ArchetypeBuilder Builder(*SM, M.getASTContext().Diags);

    // First, add the old generic signature.
    // FIXME: It does not preserve references to the declarations of generic
    // parameters known in the original generic environment. Instead, it
    // just copies the GenericTypeParameterTypes and requirements.
    // It would be nice to preserve the user-friendly names, which would
    // make the SIL generated for the specialzied function easier to understand
    // and compare with the original function.
    Builder.addGenericSignature(OrigGenSig, nullptr);

    // For each substitution with a concrete type as a replacement,
    // add a new concrete type equality requirement.
    for (auto &entry : InterfaceSubs.getMap()) {
      if (!entry.second->getCanonicalType()->hasArchetype()) {
        auto CanTy = entry.first->getCanonicalType();
        auto OutTy = CanTy;

        Builder.addSameTypeRequirementToConcrete(
            Builder.resolveArchetype(OutTy),
            entry.second->getCanonicalType(),
            RequirementSource(RequirementSource::Explicit, SourceLoc()));
      }
    }

    // Remember the new generic signature.
    SpecializedGenSig = Builder.getGenericSignature()->getCanonicalSignature();
    // Remember the new generic environment.
    SpecializedGenericEnv = Builder.getGenericEnvironment();

    llvm::dbgs() << "Created the new generic signature: \n";
    SpecializedGenSig->dump();

    llvm::dbgs() << "for function type: ";
    OrigF->getLoweredFunctionType()->dump();
    llvm::dbgs() << "with substitutions:\n";
    for (auto Sub : ParamSubs) {
      Sub.dump();
    }
    llvm::dbgs() << "\n";

    // If an archetype is mapped to a type containing an archetype, then
    // map it to itself.
    for (auto &entry : InterfaceSubs.getMap()) {
      if (entry.second->getCanonicalType()->hasArchetype()) {
        auto CanTy = entry.first->getCanonicalType();
        // Map generic parameter type to an interface type in the
        // old generic environment.
        AdjustedInterfaceSubs.replaceSubstitution(
            CanTy, OrigGenericEnv->mapTypeOutOfContext(SM, CanTy));
        // Map generic parameter type to a contextual type in the
        // old generic environment.
        AdjustedParamSubsMap.replaceSubstitution(
            CanTy, OrigGenericEnv->mapTypeIntoContext(SM, CanTy));
        // Map generic parameter type to a contextual type in the
        // new generic environment. This will be used by the cloner.
        AdjustedCloningSubs.replaceSubstitution(
            CanTy, SpecializedGenericEnv->mapTypeIntoContext(SM, CanTy));
      } else {
        // Remap to the concrete types. But it is in the map already.
      }
    }

    // Create a new list of substitutions.
    SmallVector<Substitution, 8> AdjustedSubsVector;
    SmallVector<Substitution, 8> AdjustedCloningSubsVector;
    SmallVector<Substitution, 8> SpecializedSubsVector;

    // First, get a substitution map from the original signature.
    // It is based on the substitution list from the apply site.
    auto ParamMap = OrigGenSig->getSubstitutionMap(ParamSubs);
    // Then, use this map to form a list of substitutions for creating the new
    // generic signature. These substitutions use interface types from the new
    // generic environment of the specialized function.
    // This new list may contain less elements, because generic parameter types
    // with concrete type equality requirements do not need a substitution.
    SpecializedGenSig->getSubstitutions(*SM, ParamMap, SpecializedSubsVector);

    // Form a list of substitutions for the old generic signature.
    // We need it because we changed substitutions for those generic
    // parameters, whose replacement types are generic in the original apply's
    // substitution list. Now they are mapped to themselves expressed as
    // contextual types in the original generic environment.
    // This set of substitutions will be used by the mangler.
    OrigGenSig->getSubstitutions(*SM, AdjustedParamSubsMap, AdjustedSubsVector);

    // These are the substitutions to be used by the cloner when it clones the
    // body of the original function. They are remapping types from the old
    // generic environment to contextual types in the new generic environment.
    OrigGenSig->getSubstitutions(*SM, AdjustedCloningSubs,
                              AdjustedCloningSubsVector);

    MutableArrayRef<Substitution> SpecializedSubs =
        OrigF->getModule().getASTContext().AllocateCopy(SpecializedSubsVector);

    MutableArrayRef<Substitution> AdjustedSubs =
        OrigF->getModule().getASTContext().AllocateCopy(AdjustedSubsVector);

    MutableArrayRef<Substitution> AdjustedCloningSubs =
        OrigF->getModule().getASTContext().AllocateCopy(
            AdjustedCloningSubsVector);

    AdjustedParamSubs = AdjustedSubs;
    AdjustedCloningParamSubs = AdjustedCloningSubs;
    SpecializedParamSubs = SpecializedSubs;
  }

  if (!HasUnboundGenericParams)
    SpecializedGenSig = nullptr;

  // Find out how the function type looks like after applying the provided
  // substitutions.
  SubstitutedType = createSubstitutedType(OrigF, AdjustedInterfaceSubs.getMap(),
                                          HasUnboundGenericParams);

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

  if (!HasUnboundGenericParams)
    return SILType::substFuncType(M, SM, SubstMap, OrigFnTy,
                                  /*dropGenerics = */ true);

  // Explicitly subst generic types in the parameters
  // and results.
  // TODO: Can it be done in one go instead of doing it
  // parameter-by-parameter?
  SmallVector<SILParameterInfo, 8> SubstParams;
  SubstParams.reserve(OrigFnTy->getParameters().size());
  for (auto &OrigParam : OrigFnTy->getParameters()) {
    auto NewTy = OrigParam.getType()
                     .subst(SM, SubstMap, SubstFlags::AllowLoweredTypes)
                     ->getCanonicalType();
    if (NewTy->hasArchetype())
      NewTy = OrigF->mapTypeOutOfContext(NewTy)->getCanonicalType();
    if (!NewTy->isLegalSILType())
      NewTy = M.Types.getLoweredType(NewTy).getSwiftRValueType();
    SubstParams.push_back(SILParameterInfo(NewTy, OrigParam.getConvention()));
  }

  SmallVector<SILResultInfo, 8> SubstResults;
  SubstResults.reserve(OrigFnTy->getNumAllResults());
  for (auto OrigResult : OrigFnTy->getAllResults()) {
    auto NewTy = OrigResult.getType()
                     .subst(SM, SubstMap, SubstFlags::AllowLoweredTypes)
                     ->getCanonicalType();
    if (NewTy->hasArchetype())
      NewTy = OrigF->mapTypeOutOfContext(NewTy)->getCanonicalType();
    if (!NewTy->isLegalSILType())
      NewTy = M.Types.getLoweredType(NewTy).getSwiftRValueType();
    SubstResults.push_back(SILResultInfo(NewTy, OrigResult.getConvention()));
  }

  auto SubstErrorResult = OrigFnTy->getOptionalErrorResult();
  if (SubstErrorResult.hasValue()) {
    auto NewTy = SubstErrorResult.getValue()
                     .getType()
                     .subst(SM, SubstMap, SubstFlags::AllowLoweredTypes)
                     ->getCanonicalType();
    if (NewTy->hasArchetype())
      NewTy = OrigF->mapTypeOutOfContext(NewTy)->getCanonicalType();
    if (!NewTy->isLegalSILType())
      NewTy = M.Types.getLoweredType(NewTy).getSwiftRValueType();
    SubstErrorResult =
        SILResultInfo(NewTy, SubstErrorResult.getValue().getConvention());
  }

  // FIXME: This does not replace the generic parameter types in the function
  // type even if they are known to have a concrete type due to type
  // equality requirements. This is why we explicitly substituted them in the
  // code above.
  return SILFunctionType::get(
      SpecializedGenSig, OrigFnTy->getExtInfo(), OrigFnTy->getCalleeConvention(),
      SubstParams, SubstResults, SubstErrorResult, M.getASTContext());
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
  GenericSpecializationMangler GenericMangler(Mangler, GenericFunc,
                                              FnTy,
                                              // Use adjusted substitutions, where
                                              // substitutions with generic replacements
                                              // are replaced by archetypes.
                                              ReInfo.getAdjustedParamSubstitutions(),
                                              Fragile);
  GenericMangler.mangle();
  ClonedName = Mangler.finalize();

  llvm::dbgs() << "\n\nMangled name: " << ClonedName << "\nfor function type: ";
  GenericFunc->getLoweredType().dump();
  llvm::dbgs() << "for FnTy: ";
  FnTy->dump();
  llvm::dbgs() << "for function type: ";
  GenericFunc->getLoweredFunctionType()->dump();
  llvm::dbgs() << "with substitutions:\n";
  for (auto Sub : ReInfo.getAdjustedParamSubstitutions()) {
    Sub.dump();
  }
  llvm::dbgs() << "\n";

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
      ReInfo.getAdjustedCloningParamSubstitutions(),
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

  ArrayRef<Substitution> Subs;
  if (ReInfo.getSpecializedType()->isPolymorphic())
    Subs = ReInfo.getSpecializedParamSubstitutions();

  // Create a substituted callee type.
  auto CanFnTy = dyn_cast<SILFunctionType>(
      Callee->getType().getSwiftRValueType()->getCanonicalType());
  auto CalleeSubstFnTy = CanFnTy;

  if (!Subs.empty()) {
    // FIXME: This operation does not substitute the archetypes for those
    // generic types, which have
    // concrete type equality requirements. And it does not allow for providing
    // any susbtitutions
    // for them, because the type equality requirements are present.
    CalleeSubstFnTy = CanFnTy->substGenericArgs(
        AI.getModule(), AI.getModule().getSwiftModule(),
        ReInfo.getSpecializedParamSubstitutions());
  }

  if (auto *TAI = dyn_cast<TryApplyInst>(AI)) {
    SILBasicBlock *ResultBB = TAI->getNormalBB();
    assert(ResultBB->getSinglePredecessor() == TAI->getParent());
    auto *NewTAI = Builder.createTryApply(
        Loc, Callee, SILType::getPrimitiveObjectType(CalleeSubstFnTy), Subs,
        Arguments, ResultBB, TAI->getErrorBB());
    if (StoreResultTo) {
      // The original normal result of the try_apply is an empty tuple.
      assert(ResultBB->getNumBBArg() == 1);
      Builder.setInsertionPoint(ResultBB->begin());
      fixUsedVoidType(ResultBB->getBBArg(0), Loc, Builder);


      SILArgument *Arg =
        ResultBB->replaceBBArg(0, StoreResultTo->getType().getObjectType());
      // Store the direct result to the original result address.
      Builder.createStore(Loc, Arg, StoreResultTo,
                          StoreOwnershipQualifier::Unqualified);
    }
    return NewTAI;
  }
  if (auto *A = dyn_cast<ApplyInst>(AI)) {
    auto *NewAI = Builder.createApply(
        Loc, Callee, SILType::getPrimitiveObjectType(CalleeSubstFnTy),
        CalleeSubstFnTy->getSILResult(), Subs, Arguments, A->isNonThrowing());
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
    CanSILFunctionType NewPAType =
      ReInfo.createSpecializedType(PAI->getFunctionType(), Builder.getModule());
    //SILType PTy = SILType::getPrimitiveObjectType(ReInfo.getSpecializedType());
    SILType PTy = SILType::getPrimitiveObjectType(CalleeSubstFnTy);
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
    GenericSpecializationMangler Mangler(M, OrigF,
                              ReInfo.getSubstitutedType(),
                              OrigPAI->getSubstitutions(), Fragile,
                              GenericSpecializationMangler::NotReabstracted);
    Mangler.mangle();
    ThunkName = M.finalize();
  }

  auto Loc = RegularLocation::getAutoGeneratedLocation();
  llvm::dbgs() << "\nCreate reabstraction thunk:\nName:\n" << ThunkName << "\n";
  ReInfo.getSubstitutedType().dump();

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

  SILBasicBlock *EntryBB = new (M) SILBasicBlock(Thunk);
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
  auto SpecArgIter = SpecEntryBB->bbarg_begin();
  for (unsigned Idx = 0; Idx < ReInfo.getNumArguments(); Idx++) {
    if (ReInfo.isArgConverted(Idx)) {
      if (ReInfo.isResultIndex(Idx)) {
        // Store the result later.
        SILType Ty = SpecType->getSILResult().getAddressType();
        ReturnValueAddr = new (M) SILArgument(EntryBB, Ty);
      } else {
        // Instead of passing the address, pass the loaded value.
        SILArgument *SpecArg = *SpecArgIter++;
        SILType Ty = SpecArg->getType().getAddressType();
        SILArgument *NewArg = new (M) SILArgument(EntryBB, Ty,
                                                  SpecArg->getDecl());
        auto *ArgVal = Builder.createLoad(Loc, NewArg,
                                          LoadOwnershipQualifier::Unqualified);
        Arguments.push_back(ArgVal);
      }
    } else {
      // No change to the argument.
      SILArgument *SpecArg = *SpecArgIter++;
      SILArgument *NewArg = new (M) SILArgument(EntryBB, SpecArg->getType(),
                                                SpecArg->getDecl());
      Arguments.push_back(NewArg);
    }
  }

  auto *FRI = Builder.createFunctionRef(Loc, SpecializedFunc);
  ArrayRef<Substitution> Subs;
  if (ReInfo.getSpecializedType()->isPolymorphic()) {
    // TODO: Create a substitution list for this function using
    // a proper SubstitutionMap.
    Subs = ReInfo.getSpecializedParamSubstitutions();
  }

  // Create a substituted callee type.
  auto CanFnTy = dyn_cast<SILFunctionType>(
      FRI->getType().getSwiftRValueType()->getCanonicalType());
  auto CalleeSubstFnTy = CanFnTy;

  if (!Subs.empty()) {
    CalleeSubstFnTy = CanFnTy->substGenericArgs(
        M, M.getSwiftModule(),
        ReInfo.getSpecializedParamSubstitutions());
  }
  auto FnTy = SILType::getPrimitiveObjectType(CalleeSubstFnTy);

  SILValue ReturnValue;
  if (SpecType->hasErrorResult()) {
    // Create the logic for calling a throwing function.
    SILBasicBlock *NormalBB = new (M) SILBasicBlock(Thunk);
    SILBasicBlock *ErrorBB = new (M) SILBasicBlock(Thunk);
    Builder.createTryApply(Loc, FRI, FnTy,
                           Subs, Arguments, NormalBB, ErrorBB);
    auto *ErrorVal = new (M) SILArgument(ErrorBB,
                                         SpecType->getErrorResult().getSILType());
    Builder.setInsertionPoint(ErrorBB);
    Builder.createThrow(Loc, ErrorVal);
    ReturnValue = new (M) SILArgument(NormalBB, SpecType->getSILResult());
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
        llvm::dbgs() << "\nPartial apply handling:\n";
        PAIUser->dumpInContext();
        llvm::dbgs() << "Non-equal NewPAType:\n";
        NewPAType->dump();
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
    llvm::dbgs() << "Replacing a partial apply:\n";
    PAI->dump();
    // There are some unknown users of the partial_apply. Therefore we need a
    // thunk which converts from the re-abstracted function back to the
    // original function with indirect parameters/results.
    auto *PAI = cast<PartialApplyInst>(Apply.getInstruction());
    SILBuilderWithScope Builder(PAI);
    SILFunction *Thunk = createReabstractionThunk(ReInfo, PAI, SpecializedF);
    llvm::dbgs() << "Thunk:\n";
    Thunk->dump();
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
    llvm::dbgs() << "Thunk call:\n";
    NewPAI->dump();
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
