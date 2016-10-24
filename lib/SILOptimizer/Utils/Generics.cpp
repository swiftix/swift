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

#if 0
// =============================================================================
// Creation of new generic functions
// =============================================================================

static const char * const GenericParamNames[] = {
  "T",
  "U",
  "V",
  "W",
  "X",
  "Y",
  "Z"
};

static std::pair<ArchetypeType*, GenericTypeParamDecl*>
createGenericParam(ASTContext &ctx, const char *name, unsigned index) {
  Module *M = ctx.TheBuiltinModule;
  Identifier ident = ctx.getIdentifier(name);
  ArchetypeType *archetype
    = ArchetypeType::getNew(ctx, nullptr,
                            static_cast<AssociatedTypeDecl *>(nullptr),
                            ident, ArrayRef<Type>(), Type(), false);
  auto genericParam =
    new (ctx) GenericTypeParamDecl(&M->getMainFile(FileUnitKind::Builtin),
                                   ident, SourceLoc(), 0, index);
  return std::make_pair(archetype, genericParam);
}

/// Create a generic parameter list with multiple generic parameters.
static GenericParamList *getGenericParams(ASTContext &ctx,
                                          unsigned numParameters,
                       SmallVectorImpl<ArchetypeType*> &archetypes,
                       SmallVectorImpl<GenericTypeParamDecl*> &genericParams) {
  assert(numParameters <= llvm::array_lengthof(GenericParamNames));
  assert(genericParams.empty());

  for (unsigned i = 0; i != numParameters; ++i) {
    auto archetypeAndParam = createGenericParam(ctx, GenericParamNames[i], i);
    archetypes.push_back(archetypeAndParam.first);
    genericParams.push_back(archetypeAndParam.second);
  }

  auto paramList = GenericParamList::create(ctx, SourceLoc(), genericParams,
                                            SourceLoc());
  return paramList;
}

namespace {
  class GenericSignatureBuilder {
  public:
    ASTContext &Context;

  private:
    GenericParamList *TheGenericParamList;

    SmallVector<GenericTypeParamDecl*, 2> GenericTypeParams;
    SmallVector<ArchetypeType*, 2> Archetypes;

    TypeSubstitutionMap InterfaceToArchetypeMap;

    SmallVector<TupleTypeElt, 4> InterfaceParams;
    SmallVector<Type, 4> BodyParams;

    Type InterfaceResult;
    Type BodyResult;

  public:
    GenericSignatureBuilder(ASTContext &ctx, unsigned numGenericParams = 1)
        : Context(ctx) {
      TheGenericParamList = getGenericParams(ctx, numGenericParams,
                                             Archetypes, GenericTypeParams);

      for (unsigned i = 0, e = GenericTypeParams.size(); i < e; i++) {
        auto paramTy = GenericTypeParams[i]->getDeclaredType()
            ->getCanonicalType().getPointer();
        InterfaceToArchetypeMap[paramTy] = Archetypes[i];
      }
    }

    template <class G>
    void addParameter(const G &generator) {
      InterfaceParams.push_back(generator.build(*this, false));
      BodyParams.push_back(generator.build(*this, true));
    }

    template <class G>
    void setResult(const G &generator) {
      InterfaceResult = generator.build(*this, false);
      BodyResult = generator.build(*this, true);
    }

    ValueDecl *build(Identifier name) {
      return getBuiltinGenericFunction(name, InterfaceParams, BodyParams,
                                       InterfaceResult, BodyResult,
                                       TheGenericParamList,
                                       InterfaceToArchetypeMap);
    }

    // Don't use these generator classes directly; call the make{...}
    // functions which follow this class.

    struct ConcreteGenerator {
      Type TheType;
      Type build(GenericSignatureBuilder &builder, bool forBody) const {
        return TheType;
      }
    };
    struct ParameterGenerator {
      unsigned Index;
      Type build(GenericSignatureBuilder &builder, bool forBody) const {
        return (forBody ? builder.Archetypes[Index]
                        : builder.GenericTypeParams[Index]->getDeclaredType());
      }
    };
    struct LambdaGenerator {
      std::function<Type(GenericSignatureBuilder &,bool)> TheFunction;
      Type build(GenericSignatureBuilder &builder, bool forBody) const {
        return TheFunction(builder, forBody);
      }
    };
    template <class T, class U>
    struct FunctionGenerator {
      T Arg;
      U Result;
      FunctionType::ExtInfo ExtInfo;
      Type build(GenericSignatureBuilder &builder, bool forBody) const {
        return FunctionType::get(Arg.build(builder, forBody),
                                 Result.build(builder, forBody),
                                 ExtInfo);
      }
    };
    template <class T>
    struct InOutGenerator {
      T Object;
      Type build(GenericSignatureBuilder &builder, bool forBody) const {
        return InOutType::get(Object.build(builder, forBody));
      }
    };
    template <class T>
    struct MetatypeGenerator {
      T Object;
      Optional<MetatypeRepresentation> Repr;
      Type build(GenericSignatureBuilder &builder, bool forBody) const {
        return MetatypeType::get(Object.build(builder, forBody), Repr);
      }
    };
  };
}

static GenericSignatureBuilder::ConcreteGenerator
makeConcrete(Type type) {
  return { type };
}

static GenericSignatureBuilder::ParameterGenerator
makeGenericParam(unsigned index = 0) {
  return { index };
}

template <class... Gs>
static GenericSignatureBuilder::LambdaGenerator
makeTuple(const Gs & ...elementGenerators) {
  return {
    [=](GenericSignatureBuilder &builder, bool forBody) -> Type {
      TupleTypeElt elts[] = {
        elementGenerators.build(builder, forBody)...
      };
      return TupleType::get(elts, builder.Context);
    }
  };
}

template <class T, class U>
static GenericSignatureBuilder::FunctionGenerator<T,U>
makeFunction(const T &arg, const U &result,
             FunctionType::ExtInfo extInfo = FunctionType::ExtInfo()) {
  return { arg, result, extInfo };
}

template <class T>
static GenericSignatureBuilder::InOutGenerator<T>
makeInOut(const T &object) {
  return { object };
}

template <class T>
static GenericSignatureBuilder::MetatypeGenerator<T>
makeMetatype(const T &object, Optional<MetatypeRepresentation> repr = None) {
  return { object, repr };
}

SILFunction *createFunctionWithSubstitutions(SILFunction *Orig,
                                             ArrayRef<Substitution> ParamSubs) {
  if (!hasUnboundGenericTypes(ParamSubs))
    return Orig;

  // Some of the substitutions contain unbound generic types.
  // Try to create a new generic function.

  for (auto Sub : ParamSubs) {
    if (Sub.getReplacement()->hasArchetype()) {
      // This type parameter should stay generic.
      contninue;
    }
    // This type parameter is not needed as it is concrete.
  }
}
#endif

// =============================================================================
// ReabstractionInfo
// =============================================================================

// Initialize SpecializedType iff the specialization is allowed.
ReabstractionInfo::ReabstractionInfo(SILFunction *OrigF,
                                     ArrayRef<Substitution> ParamSubs) {
  if (!OrigF->shouldOptimize()) {
    DEBUG(llvm::dbgs() << "    Cannot specialize function " << OrigF->getName()
                       << " marked to be excluded from optimizations.\n");
    return;
  }

  SubstitutionMap InterfaceSubs;
  SubstitutionMap NewInterfaceSubs;
  SubstitutionMap *FinalInterfaceSubs = &InterfaceSubs;

  if (OrigF->getLoweredFunctionType()->getGenericSignature())
    InterfaceSubs = OrigF->getLoweredFunctionType()->getGenericSignature()
      ->getSubstitutionMap(ParamSubs);

  bool HasConcreteGenericParams = false;
  bool HasUnboundGenericParams = false;
  for (auto &entry : InterfaceSubs.getMap()) {
    if (entry.second->getCanonicalType()->hasArchetype()) {
      HasUnboundGenericParams = true;
      continue;
    }
    HasConcreteGenericParams = true;
    //break;
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

  if (HasUnboundGenericParams) {
#if 1
    // Try to form a new generic signature based on the old one.
    auto OrigSig = OrigF->getLoweredFunctionType()->getGenericSignature();
    ArchetypeBuilder Builder(*OrigF->getModule().getSwiftModule(), OrigF->getModule().getASTContext().Diags);

    //Builder.addGenericSignature(OrigSig, OrigF->getGenericEnvironment(), true);
    // Add all generic parameters.
    for (auto GP : OrigSig->getGenericParams()) {
      Builder.addGenericParameter(GP);
    }

    // Add all original requirements.
    auto OrigRequirements = OrigSig->getRequirements();
    auto Source = RequirementSource(RequirementSource::Explicit, SourceLoc());
    for (auto &Req : OrigRequirements) {
      Builder.addRequirement(Req, Source);
    }

#if 1
    // For each substitution with a concrete type as a replacement,
    // add a new concrete type equality requirement.
    for (auto &entry : InterfaceSubs.getMap()) {
      if (!entry.second->getCanonicalType()->hasArchetype()) {
        auto CanTy = entry.first->getCanonicalType();
        auto OutTy = !CanTy->hasTypeParameter() ? OrigF->mapTypeOutOfContext(CanTy) : CanTy;
        //auto InTy = OrigF->mapTypeIntoContext(CanTy);

        Builder.addSameTypeRequirementToConcrete(
            Builder.resolveArchetype(OutTy),
            entry.second->getCanonicalType(),
            RequirementSource(RequirementSource::Explicit, SourceLoc()));

        //Builder.addSameTypeRequirementToConcrete(
        //    Builder.resolveArchetype(InTy),
        //    entry.second->getCanonicalType(),
        //    RequirementSource(RequirementSource::Explicit, SourceLoc()));
      }
    }
#endif
    // TODO: Minimize the generic signature?
    // I.e. if a given generic parameter is only use in a form T == concrete_type and nowhere else,
    // simply remove it.
    Builder.finalize(SourceLoc(), false);
    //Builder.minimize();
    auto NewGenSig = Builder.getGenericSignature();
    NewGenSig->dump();

    // Now, check for each generic parameter if it is only used by same concrete type requirements.
    // If this is the case, it can be removed.
    // Walk over the set of requirements and collect information about genric parameters
    // that only occur in the first type of a same concrete-type type requirement.
    // These generics params are the ones that can be eliminated.
    // TODO: Create the substitution remapping at the same time?
    auto NewRequirements = NewGenSig->getRequirements();
    llvm::DenseSet<Type> AliveGenericParams;
    auto RememberAliveGenericParams = [&AliveGenericParams] (Type ty) {
      if (isa<GenericTypeParamType>(ty.getPointer()))
        AliveGenericParams.insert(ty);
    };

    auto FindReferenceToAliveGenericParam = [&AliveGenericParams] (Type ty) -> bool {
      return AliveGenericParams.count(ty) > 0;
    };

    llvm::dbgs() << "Generic signature requirements:";
    for (auto &Req : NewRequirements) {
      llvm::dbgs() << "\nRequirement kind: " << (int)Req.getKind()
                   << "\n for type: ";
      Req.getFirstType().dump();
      llvm::dbgs() << "Requirement:\n";
      Req.dump();
      auto First = Req.getFirstType();
      switch (Req.getKind()) {
      case RequirementKind::WitnessMarker:
        continue;
      case RequirementKind::SameType: {
        auto Second = Req.getSecondType();
        if (!Second->getCanonicalType()->hasArchetype())
          continue;
        // Keep alive any generic parameter referenced in First.
        First.visit(RememberAliveGenericParams);
      }
      case RequirementKind::Conformance:
      case RequirementKind::Superclass: {
        auto Second = Req.getSecondType();
        // Keep alive any generic parameter referenced in First and Second.
        First.visit(RememberAliveGenericParams);
        Second.visit(RememberAliveGenericParams);
      }
      }
    }

    // Dump the set of used generic parameter types.
    if (!AliveGenericParams.empty()) {
      llvm::dbgs() << "Alive generic parameters:\n";
      for (auto Ty : AliveGenericParams) {
        Ty.dump();
      }
    }

    // Create a new generic signature which only contains those generic
    // parameter types which are alive.
    {
      ArchetypeBuilder Builder(*OrigF->getModule().getSwiftModule(),
                               OrigF->getModule().getASTContext().Diags);
      for (auto GP : NewGenSig->getGenericParams()) {
        if (!AliveGenericParams.count(GP))
          continue;
        Builder.addGenericParameter(GP);
      }

      // Add all original requirements.
      auto NewGenSigRequirements = NewGenSig->getRequirements();
      auto Source = RequirementSource(RequirementSource::Explicit, SourceLoc());
      for (auto &Req : NewGenSigRequirements) {
        auto First = Req.getFirstType();
        // Check if the first type refers to any alive generic parameter type.
        if (!First.findIf(FindReferenceToAliveGenericParam))
          continue;
        // Skip any requirements for the dead generic parameter types.
        Builder.addRequirement(Req, Source);
      }

      Builder.finalize(SourceLoc(), false);
      // Builder.minimize();
      llvm::dbgs() << "Final minimized generic signature:\n";
      auto FinalSig = Builder.getGenericSignature();
      FinalSig->dump();
    }

#endif

    // There are some unbound substitutions.
    auto ForwardingSubs = OrigF->getForwardingSubstitutions();
    NewInterfaceSubs = InterfaceSubs;
    FinalInterfaceSubs = &NewInterfaceSubs;
    // Remap unbound generic params to themselves.
    for (auto &entry : InterfaceSubs.getMap()) {
      if (entry.second->getCanonicalType()->hasArchetype()) {
        auto CanTy = entry.first->getCanonicalType();
#if 0
        // NewInterfaceSubs.removeType(entry.first);
        auto CanTy = entry.first->getCanonicalType();
        NewInterfaceSubs.replaceSubstitution(
            CanTy,
            (CanTy->hasArchetype() || isa<GenericTypeParamType>(CanTy))
                //? OrigF->mapTypeOutOfContext(entry.first->getCanonicalType())
                ? OrigF->mapTypeIntoContext(CanTy)
                : CanTy);
#endif
        // Do not substitute this type.
        NewInterfaceSubs.removeType(CanTy);
      } else {
        //NewInterfaceSubs.addSubstitution(entry.first->getCanonicalType(), entry.second);
      }
    }
  }

#if 0
  // We do not support partial specialization.
  if (hasUnboundGenericTypes(InterfaceSubs.getMap())) {
    DEBUG(llvm::dbgs() <<
          "    Cannot specialize with unbound interface substitutions.\n");
    DEBUG(for (auto Sub : ParamSubs) {
            Sub.dump();
          });
    return;
  }
#endif

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
      return;
    }
  }

  SILModule &M = OrigF->getModule();
  Module *SM = M.getSwiftModule();

  // Find out how the function type looks like after applying the provided
  // substitutions.
  SubstitutedType = SILType::substFuncType(M, SM, FinalInterfaceSubs->getMap(),
                                           OrigF->getLoweredFunctionType(),
                                           /*dropGenerics = */ !HasUnboundGenericParams);

  auto MappedSubstitutedType = SubstitutedType;
  auto FinalSubstitutedType = SubstitutedType;

  if (HasUnboundGenericParams) {
    // If generic signature was not dropped, then it still has the same number
    // of generic parameters as the origF's lowered function type. But the
    // actual signature of the partially specialized function should contain
    // only generic parameters for those generic typw parameters which were not
    // substituted by concrete types.
    auto SubstOrigGenSig = SubstitutedType->getGenericSignature();

    // Form a new list of generic parameters. It contains all those generic
    // parameters, which are not bound in the substitued generic signature.
    // FIXME: Can we reuse the GenericTypeParamType and requirements from
    // the existing signature.
    auto OrigGenricParams = SubstOrigGenSig->getGenericParams();
    SmallVector<GenericTypeParamType *, 4> GenericParams;
    for (auto GP : OrigGenricParams) {
      TypeBase *Ty = GP->getCanonicalType().getPointer();
      Type ReplacementTy = InterfaceSubs.getMap().lookup(Ty);
      assert(ReplacementTy);
      if (!ReplacementTy->getCanonicalType()->hasArchetype())
        continue;
      GenericParams.push_back(GP);
    }

    // Create a new generic signature with fewer generic type parameters.
    auto SubstGenSig = GenericSignature::get(
        GenericParams, SubstOrigGenSig->getRequirements());

    // Create a new substituted type, which the updated signature.
    Optional<SILResultInfo> ErrorResult;
    if (SubstitutedType->hasErrorResult())
      ErrorResult = SubstitutedType->getErrorResult();

    FinalSubstitutedType = SILFunctionType::get(
        SubstGenSig, SubstitutedType->getExtInfo(),
        SubstitutedType->getCalleeConvention(),
        SubstitutedType->getParameters(), SubstitutedType->getAllResults(),
        ErrorResult, M.getASTContext());
    // MappedSubstitutedType =
    // dyn_cast<SILFunctionType>(OrigF->mapTypeIntoContext(MappedSubstitutedType)->getCanonicalType());
    // MappedSubstitutedType = SILType::substFuncType(M, SM,
    // FinalInterfaceSubs->getMap(), SubstitutedType, false);
  }

  NumResults = FinalSubstitutedType->getNumIndirectResults();
  Conversions.resize(NumResults + FinalSubstitutedType->getParameters().size());
  // TODO: isLoadable checks assert for generic types currently.
  if (FinalSubstitutedType->getNumDirectResults() == 0) {
    // The original function has no direct result yet. Try to convert the first
    // indirect result to a direct result.
    // TODO: We could also convert multiple indirect results by returning a
    // tuple type and created tuple_extract instructions at the call site.
    unsigned IdxForResult = 0;
    for (SILResultInfo RI : SubstitutedType->getIndirectResults()) {
      assert(RI.isIndirect());
      if (!RI.getSILType().getSwiftRValueType()->hasUnboundGenericType())
      if (RI.getSILType().isLoadable(M) && !RI.getType()->isVoid()) {
        Conversions.set(IdxForResult);
        break;
      }
      ++IdxForResult;
    }
  }
  // Try to convert indirect incoming parameters to direct parameters.
  unsigned IdxForParam = NumResults;
  for (SILParameterInfo PI : SubstitutedType->getParameters()) {
    if (!PI.getSILType().getSwiftRValueType()->hasUnboundGenericType())
    if (PI.getSILType().isLoadable(M) &&
        PI.getConvention() == ParameterConvention::Indirect_In) {
      Conversions.set(IdxForParam);
    }
    ++IdxForParam;
  }
  SpecializedType = createSpecializedType(FinalSubstitutedType, M);
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
      auto C = (SILParamTy.isTrivial(M) ? ParameterConvention::Direct_Unowned :
                ParameterConvention::Direct_Owned);
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

#if 0
  if (hasUnboundGenericTypes(ParamSubs)) {
    // We need a partial specialization.
    auto NewF = createFunctionWithSubstitutions(GenericFunc, ParamSubs);
  }
#endif

  Mangle::Mangler Mangler;
  GenericSpecializationMangler GenericMangler(Mangler, GenericFunc,
                                              ParamSubs, Fragile);
  GenericMangler.mangle();
  ClonedName = Mangler.finalize();

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
  SILFunction * SpecializedF =
    GenericCloner::cloneFunction(GenericFunc, Fragile, ReInfo,
                                 ParamSubs, ClonedName);

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
        SILValue Val = Builder.createLoad(Loc, Op.get());
        Arguments.push_back(Val);
      }
    } else {
      Arguments.push_back(Op.get());
    }
    ++Idx;
  }

  if (auto *TAI = dyn_cast<TryApplyInst>(AI)) {
    SILBasicBlock *ResultBB = TAI->getNormalBB();
    assert(ResultBB->getSinglePredecessor() == TAI->getParent());
    auto *NewTAI =
      Builder.createTryApply(Loc, Callee, Callee->getType(), {},
                             Arguments, ResultBB, TAI->getErrorBB());
    if (StoreResultTo) {
      // The original normal result of the try_apply is an empty tuple.
      assert(ResultBB->getNumBBArg() == 1);
      Builder.setInsertionPoint(ResultBB->begin());
      fixUsedVoidType(ResultBB->getBBArg(0), Loc, Builder);


      SILArgument *Arg =
        ResultBB->replaceBBArg(0, StoreResultTo->getType().getObjectType());
      // Store the direct result to the original result address.
      Builder.createStore(Loc, Arg, StoreResultTo);
    }
    return NewTAI;
  }
  if (auto *A = dyn_cast<ApplyInst>(AI)) {
    auto *NewAI = Builder.createApply(Loc, Callee, Arguments, A->isNonThrowing());
    if (StoreResultTo) {
      // Store the direct result to the original result address.
      fixUsedVoidType(A, Loc, Builder);
      Builder.createStore(Loc, NewAI, StoreResultTo);
    }
    A->replaceAllUsesWith(NewAI);
    return NewAI;
  }
  if (auto *PAI = dyn_cast<PartialApplyInst>(AI)) {
    CanSILFunctionType NewPAType =
      ReInfo.createSpecializedType(PAI->getFunctionType(), Builder.getModule());
    SILType PTy = SILType::getPrimitiveObjectType(ReInfo.getSpecializedType());
    auto *NewPAI =
      Builder.createPartialApply(Loc, Callee, PTy, {}, Arguments,
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
                              OrigPAI->getSubstitutions(), Fragile,
                              GenericSpecializationMangler::NotReabstracted);
    Mangler.mangle();
    ThunkName = M.finalize();
  }

  auto Loc = RegularLocation::getAutoGeneratedLocation();
  SILFunction *Thunk =
    M.getOrCreateSharedFunction(Loc, ThunkName, ReInfo.getSubstitutedType(),
                              IsBare, IsTransparent, Fragile,
                              IsThunk);

  // Re-use an existing thunk.
  if (!Thunk->empty())
    return Thunk;

  SILBasicBlock *EntryBB = new (M) SILBasicBlock(Thunk);
  SILBuilder Builder(EntryBB);
  SILBasicBlock *SpecEntryBB = &*SpecializedFunc->begin();
  CanSILFunctionType SpecType = SpecializedFunc->getLoweredFunctionType();
  SILArgument *ReturnValueAddr = nullptr;

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
        auto *ArgVal = Builder.createLoad(Loc, NewArg);
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
  SILValue ReturnValue;
  if (SpecType->hasErrorResult()) {
    // Create the logic for calling a throwing function.
    SILBasicBlock *NormalBB = new (M) SILBasicBlock(Thunk);
    SILBasicBlock *ErrorBB = new (M) SILBasicBlock(Thunk);
    Builder.createTryApply(Loc, FRI, SpecializedFunc->getLoweredType(),
                           {}, Arguments, NormalBB, ErrorBB);
    auto *ErrorVal = new (M) SILArgument(ErrorBB,
                                         SpecType->getErrorResult().getSILType());
    Builder.setInsertionPoint(ErrorBB);
    Builder.createThrow(Loc, ErrorVal);
    ReturnValue = new (M) SILArgument(NormalBB, SpecType->getSILResult());
    Builder.setInsertionPoint(NormalBB);
  } else {
    ReturnValue = Builder.createApply(Loc, FRI, SpecializedFunc->getLoweredType(),
                                SpecType->getSILResult(), {}, Arguments, false);
  }
  if (ReturnValueAddr) {
    // Need to store the direct results to the original indirect address.
    Builder.createStore(Loc, ReturnValue, ReturnValueAddr);
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
