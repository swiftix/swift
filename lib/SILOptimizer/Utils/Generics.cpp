//===- Generics.cpp ---- Utilities for transforming generics ----*- C++ -*-===//
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

#define DEBUG_TYPE "generic-specializer"

#include "swift/Strings.h"
#include "swift/SILOptimizer/SpecializationsAnalysis.h"
#include "swift/SILOptimizer/Utils/Generics.h"
#include "swift/SILOptimizer/Utils/GenericCloner.h"

#include "llvm/ADT/Statistic.h"
STATISTIC(NumSpecializations, "Number of specializations");
STATISTIC(NumSharedSpecializations, "Number of shared specializations");

using namespace swift;

// Create a new apply based on an old one, but with a different
// function being applied.
SpecializationResult swift::replaceWithSpecializedFunction(ApplySite AI,
                                                           SILFunction *NewF) {
  // TODO: Cast input arguments as required by NewF
  //       Cast return value as required by the original apply site.
  ApplySite NewAI;
  SILLocation Loc = AI.getLoc();

  ArrayRef<Substitution> Subs;
  CanSILFunctionType SubstFnTy = NewF->getLoweredFunctionType();

  if (SubstFnTy->isPolymorphic()) {
    Subs = AI.getSubstitutions();
    SubstFnTy = SubstFnTy->substGenericArgs(
                  AI.getModule(), AI.getModule().getSwiftModule(), Subs);
  }

  CanSILFunctionType OrigSubstFnTy = AI.getSubstCalleeType();
  SILBuilderWithScope Builder(AI.getInstruction());

  SILValue NewCallee = Builder.createFunctionRef(Loc, NewF);

  if (OrigSubstFnTy != SubstFnTy) {
    // If the new callee does not match the type of original callee,
    // make it match! This may happen is we reuse a shared specialization.
    // This makes a call well-formed from the type system point of view.
    // FIXME: But if this function is being inlined later, then the cloner would
    // still run into problems, when it will substitute arguments and suddenly
    // detect that types of arguments do not match types of some instructions.
    //NewCallee = Builder.createConvertFunction(AI.getLoc(), NewCallee, OrigSubstFnTy);
    //NewCallee = Builder.createUncheckedBitCast(AI.getLoc(), NewCallee, AI.getSubstCalleeSILType());
    //SubstFnTy = OrigSubstFnTy;
  }

  SILFunctionType::ParameterSILTypeArrayRef ReqParamTypes = ArrayRef<SILParameterInfo>();
  SILFunctionType::ParameterSILTypeArrayRef OrigParamTypes = ArrayRef<SILParameterInfo>();
  if (SubstFnTy) {
    ReqParamTypes = SubstFnTy->getParameterSILTypes();
    OrigParamTypes = AI.getSubstCalleeType()->getParameterSILTypes();
    assert(ReqParamTypes.size() == OrigParamTypes.size() && "Wrong number of parameters");
  }
  auto CallArguments = AI.getArguments();

  // NOTE: We need to cast arguments only if we replace a call by call of
  // a shared specializations, whose type are layout compatible, but may
  // be incompatible in terms of safe casting.
  SmallVector<SILValue, 4> Arguments;
  for (int i = 0, e = CallArguments.size(); i < e; ++i) {
    auto Arg = CallArguments[i];
#if 0
    if (SubstFnTy) {
      auto ReqParamTy = ReqParamTypes[ReqParamTypes.size() - e + i];
      if (ReqParamTy != Arg.getType()) {
        // Cast the argument.
        llvm::dbgs() << "Casting argument: ";
        Arg.dump();
        llvm::dbgs() << "From type: " << Arg.getType() << " to type: " << ReqParamTy << "\n";
//        if (canCastValueToABICompatibleType(Builder.getModule(), Arg.getType(), ReqParamTy))
//          Arg = castValueToABICompatibleType(&Builder, AI.getLoc(), Arg, Arg.getType(), ReqParamTy).getValue();
//        else {
//          if (ReqParamTy.isAddress())
//            Arg = Builder.createUncheckedAddrCast(AI.getLoc(), Arg, ReqParamTy);
//          // Force a bitcast
//          else
//            Arg = Builder.createUncheckedBitwiseCast(AI.getLoc(), Arg, ReqParamTy);
//        }
//        if (ReqParamTy.isObject() && Arg.getType().isObject())
//          Arg = Builder.createUncheckedRefCast(AI.getLoc(), Arg, ReqParamTy);
//        else
//          if (isa<MetatypeType>(ReqParamTy.getSwiftRValueType()))
//          Arg = Builder.createUncheckedBitwiseCast(AI.getLoc(), Arg, ReqParamTy);
//        else
        if (ReqParamTy.isAddress())
          Arg = Builder.createUncheckedAddrCast(AI.getLoc(), Arg, ReqParamTy);
        else
          Arg = Builder.createUncheckedBitwiseCast(AI.getLoc(), Arg, ReqParamTy);
        llvm::dbgs() << "Instruction : " << Arg <<  "\n";
      }
    }
#endif
    Arguments.push_back(Arg);
  }

  if (auto *TAI = dyn_cast<TryApplyInst>(AI)) {
    NewAI = Builder.createTryApply(Loc, NewCallee,
                                   //NewCallee.getType(),
                                   TAI->getSubstCalleeSILType(),
                                   Subs, Arguments, TAI->getNormalBB(),
                                   TAI->getErrorBB());
    return std::make_pair(nullptr, NewAI);
  } else if (auto *Apply = dyn_cast<ApplyInst>(AI)) {
    if (!Subs.empty()) {
      auto SILResultTy = SubstFnTy->getSILResult();
//      auto ReqSILResultTy = AI.getOrigCalleeType()->substGenericArgs(
//                  AI.getModule(), AI.getModule().getSwiftModule(),
//                  Subs)->getSILResult();
      // TODO: Result type should also use substitutions?
      NewAI = Builder.createApply(Loc, NewCallee,
                                 Apply->getSubstCalleeSILType(),
//                                 Apply->getModule().Types.getLoweredType(SubstFnTy),
////                                 NewF->getLoweredType().substGenericArgs(AI.getModule(), Subs),
                                 SILResultTy, Subs, Arguments,
                                 Apply->isNonThrowing());
//      if (SILResultTy != ReqSILResultTy) {
//        // Cast the result.
//        return Builder.createUncheckedBitCast(AI.getLoc(), NewAI, ReqSILResultTy);
//      }
//      return NewAI;
    }
    else
      NewAI = Builder.createApply(Loc, NewCallee, Arguments, Apply->isNonThrowing());
  } else if (auto *PAI = dyn_cast<PartialApplyInst>(AI))
      NewAI = Builder.createPartialApply(Loc, NewCallee,
                                         //NewCallee.getType(),
                                         PAI->getSubstCalleeSILType(),
                                         Subs,
                                         Arguments,
                                        PAI->getType()
                                        //SILBuilder::getPartialApplyResultType(NewCallee.getType(), CallArguments.size(), AI.getModule(), Subs)
                                        );
  else
    llvm_unreachable("unhandled kind of apply");

  auto OrigResultTy = AI.getSubstCalleeType()->getSILResult();

  SILValue ResultValue;
#if 1
  ResultValue = NewAI.getInstruction();
#else
  if (canCastValueToABICompatibleType(Builder.getModule(), NewAI.getType(), OrigResultTy))
    ResultValue = castValueToABICompatibleType(&Builder, NewAI.getLoc(),
        NewAI.getInstruction(), NewAI.getType(), OrigResultTy).getValue();
  else {
    // Force a bitcast
    if (OrigResultTy.isAddress())
      ResultValue = Builder.createUncheckedAddrCast(AI.getLoc(), NewAI.getInstruction(), OrigResultTy);
    else
      ResultValue = Builder.createUncheckedBitwiseCast(AI.getLoc(), NewAI.getInstruction(), OrigResultTy);
  }
#endif
  // Verify if the transformation was OK.
  NewAI.getFunction()->verify();

  return std::make_pair(ResultValue.getDef(), NewAI);
}


/// Try to convert definition into declaration.
static bool convertExtenralDefinitionIntoDeclaration(SILFunction *F) {
  // Bail if it is a declaration already.
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
  F->convertToDeclaration();
  assert(F->isExternalDeclaration() &&
         "Function should be an external declaration");

  DEBUG(llvm::dbgs() << "  removed external function " << F->getName() << "\n");

  return true;
}

/// Check of a given name could be a name of a white-listed
/// specialization.
bool swift::isWhitelistedSpecialization(StringRef SpecName) {
  // The whitelist of classes and functions from the stdlib,
  // whose specializations we want to preserve.
  ArrayRef<StringRef> Whitelist = {
      "Array",
      "_ArrayBuffer",
      "_ContiguousArrayBuffer",
      "Range",
      "RangeGenerator",
      "_allocateUninitializedArray",
      "UTF8",
      "UTF16",
      "String",
      "_StringBuffer",
      "_toStringReadOnlyPrintable",
  };

  // TODO: Once there is an efficient API to check if
  // a given symbol is a specialization of a specific type,
  // use it instead. Doing demangling just for this check
  // is just wasteful.
  auto DemangledNameString =
     swift::Demangle::demangleSymbolAsString(SpecName);

  StringRef DemangledName = DemangledNameString;

  auto pos = DemangledName.find("generic ", 0);
  if (pos == StringRef::npos)
    return false;

  // Create "of Swift"
  llvm::SmallString<64> OfString;
  llvm::raw_svector_ostream buffer(OfString);
  buffer << "of ";
  buffer << STDLIB_NAME <<'.';

  StringRef OfStr = buffer.str();

  pos = DemangledName.find(OfStr, pos);

  if (pos == StringRef::npos)
    return false;

  pos += OfStr.size();

  for(auto Name: Whitelist) {
    auto pos1 = DemangledName.find(Name, pos);
    if (pos1 == pos && !isalpha(DemangledName[pos1+Name.size()])) {
      return true;
    }
  }

  return false;
}

/// Cache a specialization.
/// For now, it is performed only for specializations in the
/// standard library. But in the future, one could think of
/// maintaining a cache of optimized specializations.
///
/// Mark specializations as public, so that they can be used
/// by user applications. These specializations are supposed to be
/// used only by -Onone compiled code. They should be never inlined.
static bool cacheSpecialization(SILModule &M, SILFunction *F) {
  // Do not remove functions from the white-list. Keep them around.
  // Change their linkage to public, so that other applications can refer to it.

  if (M.getOptions().Optimization >= SILOptions::SILOptMode::Optimize &&
      F->getLinkage() != SILLinkage::Public &&
      F->getModule().getSwiftModule()->getName().str() == STDLIB_NAME) {
    if (F->getLinkage() != SILLinkage::Public &&
        isWhitelistedSpecialization(F->getName())) {

      DEBUG(
        auto DemangledNameString =
          swift::Demangle::demangleSymbolAsString(F->getName());
        StringRef DemangledName = DemangledNameString;
        llvm::dbgs() << "Keep specialization: " << DemangledName << " : "
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
      return true;
    }
  }
  return false;
}

/// Register a new specialization:
/// - Remember what was the original non-specialized function
/// - Add this specialization to the set of specializations of
///   the original non-specialized function.
/// - Remember which substitutions were used to produce this
///   specialization.
static void registerSpecialization(SILModule &M, SILFunction *OrigF,
                                   SILFunction *Specialization,
                                   ArrayRef<Substitution> Substitutions,
                                   SpecializationsAnalysis *SA) {
  auto &SI = SA->getOrBuildSpecializationsInfo();
  SI.registerSpecialization(OrigF, Specialization, Substitutions);

//  auto &SpecInfo = SI.getSpecializationInfo(Specialization);
//  SmallVectorImpl<SymbolicLayout> &LayoutsF = SpecInfo.getLayouts();
//  for (auto Sub: Substitutions) {
//    auto size = computeSymbolicLayout(Sub.getReplacement(), &M);
//    llvm::dbgs() << "Type " << Sub.getArchetype()->getName() << "=" << Sub.getReplacement() << " : " << size << "\n";
//    llvm::dbgs() << "Layout encoding: " << size << "\n";
//    LayoutsF.push_back(size);
//  }
}

static unsigned getFunctionSize(SILFunction *F) {
  unsigned size = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++size;
  return size;
}

//static bool needsSpecialization(SILFunction *F, SpecializationsInfo &SI) {
//  getSpecializationSharingKind(F);
//}

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
  // TODO: Only check that this function exists, but don't read
  // its body. It can save some compile-time.
  if (isWhitelistedSpecialization(FunctionName) &&
      M.linkFunction(FunctionName, SILOptions::LinkingMode::LinkNormal))
    return M.lookUpFunction(FunctionName);

  return nullptr;
}

SILFunction *swift::getExistingSpecialization(SILModule &M,
                                              StringRef FunctionName) {
  auto *Specialization = lookupExistingSpecialization(M, FunctionName);
  if (!Specialization)
    return nullptr;
  if (hasPublicVisibility(Specialization->getLinkage())) {
    // The bodies of existing specializations cannot be used,
    // as they may refer to non-public symbols.
    if (Specialization->isDefinition())
      Specialization->convertToDeclaration();
    Specialization->setLinkage(SILLinkage::PublicExternal);
    // Ignore body for -Onone and -Odebug.
    assert((Specialization->isExternalDeclaration() ||
            convertExtenralDefinitionIntoDeclaration(Specialization)) &&
           "Could not remove body of the found specialization");
    if (!convertExtenralDefinitionIntoDeclaration(Specialization)) {
      DEBUG(
          llvm::dbgs() << "Could not remove body of specialization: "
                       << FunctionName << '\n');
    }

    DEBUG(
        llvm::dbgs() << "Found existing specialization for: "
                     << FunctionName << '\n';
        llvm::dbgs() << swift::Demangle::demangleSymbolAsString(
                            Specialization->getName()) << "\n\n");
  } else {
    // Forget about this function.
    DEBUG(llvm::dbgs() << "Cannot reuse the specialization: "
           << swift::Demangle::demangleSymbolAsString(Specialization->getName())
           <<"\n");
    return nullptr;
  }

  return Specialization;
}

// Only classes can be shared with AnyObject.
static bool canBeSharedWithAnyObject(Type Ty, SILModule &M) {
//  return SILType::isPointerSizeAndAligned(Ty.getCanonicalTypeOrNull());
  //Ty.getCanonicalTypeOrNull().isAnyClassReferenceType();
  return SILType::getPrimitiveObjectType(Ty.getCanonicalTypeOrNull()).isReferenceCounted(M);
  //return Ty.getCanonicalTypeOrNull().getClassOrBoundGenericClass();
}

static bool canBeSharedWithAnotherType(Type Ty, SILModule &M) {

  static bool isInitialized = false;

  if (!isInitialized) {
    isInitialized = true;
    for (SILFunction &F: M) {
      auto LoweredFnTy = F.getLoweredFunctionType();
      // Iterate over each parameter
      auto ParamSILTypes = LoweredFnTy->getParameterSILTypes();
      for (auto ParamSILTy: ParamSILTypes) {
        auto size = computeSymbolicLayout(ParamSILTy.getSwiftRValueType(), &M);
      }
      auto ResultSILTy = LoweredFnTy->getSILResult();
      auto size = computeSymbolicLayout(ResultSILTy.getSwiftRValueType(), &M);
    }
  }

  // Compute the symbolic size of Ty.
  // Check if there is another known specialization with a type Ty2,
  // which has the same symbolic size.
  auto size = computeSymbolicLayout(Ty, &M);
  return false;
}

/// Clone the generic parameters list and add new requirements into the clone.
static GenericParamList *cloneWithAdditionalRequirements(const ASTContext &Context,
                                                  GenericParamList *GPList,
                                                  ArrayRef<RequirementRepr> Requirements) {
  SmallVector<RequirementRepr, 4> NewRequirements;

  for (auto Req: GPList->getRequirements()) {
    NewRequirements.push_back(Req);
  }

  for (auto Req: Requirements) {
    NewRequirements.push_back(Req);
  }

  auto clone = GPList->create(Context,
                      SourceLoc(),
                      GPList->getParams(),
                      SourceLoc(),
                      NewRequirements,
                      SourceLoc());
  clone->setAllArchetypes(GPList->getAllArchetypes());
  clone->setOuterParameters(GPList->getOuterParameters());
  return clone;
}

static GenericParamList *createGenericParamList(const ASTContext &Context,
                                                  GenericParamList *GPList,
                                                  ArrayRef<GenericTypeParamDecl *> Params,
                                                  ArrayRef<RequirementRepr> Requirements) {
  SmallVector<RequirementRepr, 4> NewRequirements;

  for (auto Req: Requirements) {
    NewRequirements.push_back(Req);
  }

  auto clone = GenericParamList::create(Context,
                      SourceLoc(),
                      Params,
                      SourceLoc(),
                      NewRequirements,
                      SourceLoc());
  //clone->setAllArchetypes(GPList->getAllArchetypes());
  clone->setOuterParameters(GPList->getOuterParameters());
  return clone;
}

static void prepareSharedSpecialization(ApplySite Apply,
                                        SILFunction *F,
                                        SmallVectorImpl<Substitution> &NewSubs,
                                        GenericParamList *&ContextGenericParams,
                                        CanSILFunctionType &LoweredFnTy) {
  /*
  // Try to produce a specialization for T: AnyObject.
  llvm::dbgs() << "\n\nSpecialization of function ";
  Apply.getCallee().dump();
  llvm::dbgs() << " could be reused for substitutions:\n";
  for (auto Sub: Substitutions) {
    Sub.dump();
  }
  */
  auto &Ctx = Apply.getModule().getASTContext();
  auto *AnyObjectProtocol = Ctx.getProtocol(KnownProtocolKind::AnyObject);
  auto Substitutions = Apply.getSubstitutions();
  LoweredFnTy = F->getLoweredFunctionType();

  SmallVector<CanArchetypeType, 4> NewArchetypes;
  GenericSignature *NewSig = nullptr;

  if (true) {
    // Create a new generic parameter list and function signature,
    // which introduce additional requirements on the archetypes,
    // i.e. introduce a conformance to AnyObject.
    // TODO: Should we use ArchetypeBuilder here to make it more robust?
    // TODO: Do we need to create new archetypes?
    GenericParamList *List = F->getContextGenericParams();

    SmallVector<RequirementRepr, 4> NewRequirementsRepr;
    SmallVector<Requirement, 4> NewRequirements;
    SmallVector<GenericTypeParamDecl *, 4> GenericParamDecls;

    assert(List->getRequirements().empty() &&
           "There should be no requirements");

    // For each generic parameter T add an additional conformance T:AnyObject.
    for (auto GP: *List) {
      auto ArcheTy = GP->getArchetype();
      // Create a new archetype.
      SmallVector<ProtocolDecl*, 1> ConformsTo;
      for (auto P: ArcheTy->getConformsTo()) {
        ConformsTo.push_back(P);
      }

      // Explicitly add AnyObject as a protocol.
      ConformsTo.push_back(AnyObjectProtocol);

      auto NewArchetype = ArchetypeType::getNew(
          Ctx, ArcheTy->getParent(), ArcheTy->getAssocTypeOrProtocol(),
          ArcheTy->getName(), ConformsTo, ArcheTy->getSuperclass(), ArcheTy->getIsRecursive());

//      auto LoweredArchetype = Apply.getModule().Types.getLoweredType(NewArchetype, 0);

      GenericTypeParamDecl *NewGP = new (Ctx) GenericTypeParamDecl(
          GP->getDeclContext(), GP->getName(), GP->getNameLoc(), GP->getDepth(), GP->getIndex());
      NewGP->setArchetype(NewArchetype);
//      NewGP->setArchetype(LoweredArchetype.castTo<ArchetypeType>());

      GenericParamDecls.push_back(NewGP);
      NewArchetypes.push_back(NewArchetype);

#ifndef NDEBUG
      if (Ctx.ArchetypeContexts.count(NewArchetype) == 0)
        Ctx.ArchetypeContexts[NewArchetype] = Ctx.ArchetypeContexts.lookup(ArcheTy);
#endif

      // Create a new GenericParam with a new archetype.
      NewRequirementsRepr.push_back(RequirementRepr::getConformance(TypeLoc::withoutLoc(NewGP->getDeclaredType()), NewGP->getLoc(),
          TypeLoc::withoutLoc(AnyObjectProtocol->getDeclaredInterfaceType())));
    }

    // Create a new generic parameter list, which includes additional requirements.
    //ContextGenericParams = cloneWithAdditionalRequirements(Ctx, List, NewRequirementsRepr);
    ContextGenericParams = createGenericParamList(Ctx, List, GenericParamDecls, NewRequirementsRepr);
    SmallVector<ArchetypeType*, 16> TmpDerivedBuffer;
    GenericParamList::deriveAllArchetypes(ContextGenericParams->getParams(),
                                          TmpDerivedBuffer);

    auto DerivedBuffer = Ctx.AllocateCopy(TmpDerivedBuffer);

    ContextGenericParams->setAllArchetypes(DerivedBuffer);

#if 1
    //    ContextGenericParams->deriveAllArchetypes();
    llvm::DenseMap<ArchetypeType*, Type> archetypeMap;

    NewSig
      = ContextGenericParams->getAsCanonicalGenericSignature(archetypeMap, Ctx);
#else
    // Create a new generic signature, which includes additional requirements.
    GenericSignature *Sig = F->getLoweredFunctionType()->getGenericSignature();
    auto GenParams = Sig->getGenericParams();
    for (auto GenericTypeParamTy: GenParams) {
      NewRequirements.push_back(Requirement(RequirementKind::WitnessMarker,
          GenericTypeParamTy, Type()));
      NewRequirements.push_back(Requirement(RequirementKind::Conformance,
          GenericTypeParamTy, AnyObjectProtocol->getDeclaredInterfaceType()));
    }

    GenericSignature *NewSig = GenericSignature::get(Sig->getGenericParams(), NewRequirements);

    ArchetypeBuilder AB(*Apply.getModule().getSwiftModule(), Ctx.Diags);
    AB.addGenericSignature(NewSig, false);
#endif

  }



  // Invoke the AnyObject version of this function instead.
  int idx = 0;
  for (auto Sub: Substitutions) {
#if 0
    // For each generic parameter T, create new archetype with an
    // additional requirement T':AnyObject and use it as
    // a replacement for T in the substitution.

    // Build conformance T:AnyObject
    //auto *Conformance = Ctx.getConformance(
    //    Sub.getReplacement(), AnyObjectProtocol, AnyObjectProtocol->getLoc(), nullptr, ProtocolConformanceState::Complete);
//      Substitution S(Sub.getArchetype(), Type(), Conformance);

    llvm::SmallString<64> NewName;
    llvm::raw_svector_ostream buffer(NewName);
    auto *Archetype = Sub.getArchetype();
    buffer << "New" << Archetype->getName().str();
    //StringRef NewNameStr(NewName);
    auto NewNameId = Ctx.getIdentifier(buffer.str());
    ///auto NewNameId = Archetype->getName();

    SmallVector<ProtocolDecl*, 1> ConformsTo;
    ConformsTo.push_back(AnyObjectProtocol);


    // Create a new archetype. Replace the old unrestricted archetype
    // by a new archetype T':AnyObject.
    // TODO: This new archetype should be wired into the function signature
    // and type.
    auto NewArchetype = ArchetypeType::getNew(
        Ctx, Archetype->getParent(), Archetype->getAssocTypeOrProtocol(),
        NewNameId, ConformsTo, Archetype->getSuperclass(), Archetype->getIsRecursive());


//      Substitution S(Sub.getArchetype(), Sub.getArchetype(), Conformance);
    Substitution S(Sub.getArchetype(), NewArchetype, {});
//      Substitution S(Sub.getArchetype(), Sub.getArchetype(), {});
    NewSubs.push_back(S);
#else
    Substitution S(Sub.getArchetype(), NewArchetypes[idx++], {});
    NewSubs.push_back(S);
//      NewSubs.push_back(Sub);
#endif
  }
  Substitutions = NewSubs;

  CanSILFunctionType OrigLoweredFnTy = F->getLoweredFunctionType();
  //OrigLoweredFnTy = OrigLoweredFnTy->substGenericArgs(Apply.getModule(), Apply.getModule().getSwiftModule(), Substitutions, false);

  SILType SILLoweredFnTy = SILType::getPrimitiveObjectType(OrigLoweredFnTy);
  TypeSubstitutionMap SubstMap = ContextGenericParams->getSubstitutionMap(Substitutions);

  SILType NewSILLoweredFnTy  = SILLoweredFnTy.subst(Apply.getModule(), Apply.getModule().getSwiftModule(), SubstMap);

  SmallVector<SILParameterInfo, 4> NewParameters;
  auto Parameters = OrigLoweredFnTy->getParameters();
  idx = 0;
  for (auto Param: Parameters) {
    if (false && Param.getSILType().hasTypeParameter()) {
      //auto Ty = SubstMap.lookup(Param.getType().getPointer());
      auto Ty = ContextGenericParams->getParams()[idx++]->getType();
      auto SILTy = Apply.getModule().Types.getLoweredType(Ty);
      CanType ParamTy(Ty);
      if (auto MetaTy = dyn_cast<MetatypeType>(ParamTy)) {
        ParamTy = CanType(MetaTy->getInstanceType());
      }
//        auto SILTy = Apply.getModule().Types.getLoweredType(Ty);
//        CanType ParamTy = SILTy.getSwiftRValueType();
//  //      CanType ParamTy(Ty);
      NewParameters.push_back(SILParameterInfo(ParamTy, Param.getConvention()));
    } else {
      NewParameters.push_back(SILParameterInfo(Param.getType(), Param.getConvention()));
    }
  }

  // TODO: Parameter types should use the new type created for the new archetype.
  LoweredFnTy = SILFunctionType::get(NewSig, OrigLoweredFnTy->getExtInfo(),
      OrigLoweredFnTy->getCalleeConvention(),
      NewParameters, //OrigLoweredFnTy->getParameters(),
      OrigLoweredFnTy->getResult(),
      OrigLoweredFnTy->hasErrorResult()? Optional<SILResultInfo>(OrigLoweredFnTy->getErrorResult()) : None,
      Ctx);
}

SpecializationResult swift::trySpecializeApplyOfGeneric(ApplySite Apply,
                                              SILFunction *&NewFunction,
                                             CloneCollector &Collector,
                                           SpecializationsAnalysis *SA) {

  NewFunction = nullptr;

  assert(Apply.hasSubstitutions() && "Expected an apply with substitutions!");

  auto *F = cast<FunctionRefInst>(Apply.getCallee())->getReferencedFunction();
  assert(F->isDefinition() && "Expected definition to specialize!");

  if (!F->shouldOptimize()) {
    DEBUG(llvm::dbgs() << "    Cannot specialize function " << F->getName()
                       << " marked to be excluded from optimizations.\n");
    return std::make_pair(nullptr, ApplySite());
  }

  auto LoweredFnTy = F->getLoweredFunctionType();
  auto Signature = LoweredFnTy->getGenericSignature();
  assert(Signature && "Function has no generic signature");

  DEBUG(llvm::dbgs() << "  ApplyInst: " << *Apply.getInstruction());

  // Create the substitution maps.
  TypeSubstitutionMap InterfaceSubs;
  TypeSubstitutionMap ContextSubs;

  // TODO: Support partial specialization, where just a subset of
  // generic parameters is substituted and the rest of generic
  // parameters stays untouched.
  // Untouched parameters could be probably represented by substitutions,
  // whose replacements are empty?

  // TODO: Check if we can re-use a shared specializaiton.
  // For example, the Array[AnyObject] specialization can be used for any
  // Array[CustomClass] specialization.
  auto Substitutions = Apply.getSubstitutions();

  bool Sharing = false;

  GenericParamList *ContextGenericParams = nullptr;
  LoweredFnTy = CanSILFunctionType();

#if 0
  SmallVector<Substitution, 8> NewSubs;
  if (canBeShared(Apply)) {
    llvm::dbgs() << "\nSpecialization could be shared:\n";
    Apply.getInstruction()->dumpInContext();
    // Just check if this specialization can be potentially shared.
    // Sharing = true;
    //prepareSharedSpecialization(Apply, F, NewSubs, ContextGenericParams, LoweredFnTy);
  }
#endif

  if (F->getLoweredFunctionType()->getGenericSignature())
    InterfaceSubs = F->getLoweredFunctionType()->getGenericSignature()
      ->getSubstitutionMap(Substitutions);


  if (F->getContextGenericParams())
    ContextSubs = F->getContextGenericParams()
      ->getSubstitutionMap(Substitutions);

  // We do not support partial specialization.
  if (!Sharing && hasUnboundGenericTypes(InterfaceSubs)) {
    DEBUG(llvm::dbgs() << "    Can not specialize with interface subs.\n");
    return std::make_pair(nullptr, ApplySite());
  }

  if (hasDynamicSelfTypes(InterfaceSubs)) {
    DEBUG(llvm::dbgs() << "    Cannot specialize with dynamic self.\n");
    return std::make_pair(nullptr, ApplySite());
  }

  // Is is a shared specialization? If so, there is no need to specialize it further.
  if (F->getName().startswith("_New_")) {
    DEBUG(llvm::dbgs() << "    Cannot specialize partially specialized functions.\n");
    return std::make_pair(nullptr, ApplySite());
  }


  llvm::SmallString<64> ClonedName;
  {
    llvm::raw_svector_ostream buffer(ClonedName);
    if (!Sharing) {
      ArrayRef<Substitution> Subs = Substitutions;
      Mangle::Mangler M(buffer);
      Mangle::GenericSpecializationMangler Mangler(M, F, Subs);
      Mangler.mangle();
    } else {
      buffer << "_New_" << F->getName().str();
    }
  }

  auto &M = Apply.getInstruction()->getModule();
  // If we already have this specialization, reuse it.
  auto NewF = M.lookUpFunction(ClonedName);

  bool couldBeShared = false;
  SILFunction *sharedF = nullptr;

  if (!NewF) {
#if 1
    // Try to find a specialization that can be shared with this one.
    NewF = SA->getOrBuildSpecializationsInfo().findSpecialization(M, F, Substitutions);
    if (NewF) {
      couldBeShared = true;
      sharedF = NewF;
    }
    if (!NewF) {
      llvm::dbgs() << "Specialization cannot be shared for function " << ClonedName << "\n";
    }
    if (NewF == F) {
      // This function is not supposed to be specialized.
      llvm::dbgs() << "Specialization can be shared.\nBut function is not supposed to be specialized: " << F->getName() << "\n";
      llvm::dbgs() << "Shared function size is: " << getFunctionSize(F) << " SIL instructions\n";
      //return std::make_pair(nullptr, ApplySite());
      NewF = nullptr;
    }
    if (NewF) {
      // TODO: Print substitutions for both functions.
      // There is a specialization that can be shared with this one.
      llvm::dbgs() << "\n\nSpecialization " << ClonedName << " for function : " << F->getName() << " can be shared with\n";
      llvm::dbgs() << "Specialization: " << NewF->getName() << "\n";
      llvm::dbgs() << "Shared function size is: " << getFunctionSize(F) << " SIL instructions\n";
      // We are only testing if they can be shared, but we do not enforce it yet.
      NewF = nullptr;
    }
#endif
  }

  if (NewF) {
#if 0
#ifndef NDEBUG
    // Make sure that NewF's subst type matches the expected type.
    auto Subs = Substitutions;
    auto FTy = (Sharing) ? LoweredFnTy:
          F->getLoweredFunctionType()->substGenericArgs(M,
                                                    M.getSwiftModule(),
                                                    Subs, !Sharing);

    assert(FTy == NewF->getLoweredFunctionType() &&
           "Previously specialized function does not match expected type.");
#endif
#endif
  } else {

    // Do not create any new specializations at Onone.
    if (M.getOptions().Optimization <= SILOptions::SILOptMode::None)
      return std::make_pair(nullptr, ApplySite());

    llvm::dbgs() << "Create specialization " << ClonedName << " for function : " << F->getName() << "\n";

    DEBUG(llvm::dbgs() << "    Specialized function " << ClonedName << '\n');

    llvm::dbgs() << "\n\nSpecialized function " << ClonedName << '\n';
    llvm::dbgs() << "Substitutions: ";
    for (auto Sub: Substitutions) {
      Sub.dump();
    }


#if 0
  SmallVector<Substitution, 8> NewSubs;
  NumSpecializations++;
  if (isGenericTypeLayoutIndependent(F)) {
    // This specialization is independent of the size of generic
    // type parameters. Hence, it can be shared for any types
    // of generic parameters.
    NumSharedSpecializations++;
    llvm::dbgs() << "\nSpecialization could be shared:\n";
    Apply.getInstruction()->dumpInContext();
    // Just check if this specialization can be potentially shared.
    // Sharing = true;
    //prepareSharedSpecialization(Apply, F, NewSubs, ContextGenericParams, LoweredFnTy);
  } else {
    // There is something depending on the size of generic type arguments.
    // Figure out the sizes of this specific specialization.
    llvm::dbgs() <<"\nSpecialization is size dependent on the generic type parameters:\n";
    for (auto Sub: Substitutions) {
      auto size = computeSymbolicLayout(Sub.getReplacement(), M);
      llvm::dbgs() << "Type " << Sub.getArchetype()->getName() << "=" << Sub.getReplacement() << " : " << size << "\n";
      llvm::dbgs() << "Layout encoding: " << size << "\n\n\n";
    }
  }
#endif

    DEBUG(
      if (M.getOptions().Optimization <= SILOptions::SILOptMode::Debug) {
        llvm::dbgs() << "Creating a specialization: " << ClonedName << "\n"; });

    // Create a new function.
    if (!Sharing)
      NewF = GenericCloner::cloneFunction(F, InterfaceSubs, ContextSubs,
          LoweredFnTy, ContextGenericParams,
          ClonedName, Apply, Substitutions,
          !Sharing, Collector.getCallback());
    else {
      // Clone the function as is, without any substitutions.
      // Only the name, generic parameter list and the signature
      // of the function is going to be changed.
      TypeSubstitutionMap EmptyMap;
      NewF = GenericCloner::cloneFunction(F, EmptyMap, EmptyMap,
          LoweredFnTy, ContextGenericParams,
          ClonedName, Apply, Substitutions, //{}, //
          !Sharing, Collector.getCallback());
    }

//    for (auto &P : Collector.getApplyPairs())
//      NewApplyPairs.push_back(P);

    NewFunction = NewF;

    llvm::dbgs() << "Created specialization size is: " << getFunctionSize(NewF) << " SIL instructions\n";

    if (couldBeShared) {
      // Introduce a marker indicating that a given specialization
      // could be shared with an existing one.
      //if (NewF->getSemanticsAttr().empty()) {
        // TODO: Add a reference to the actual shared method to be used?
        //
        // IRGen could then emit for the current method a body consisting of
        // a single instruction which just jumps to that method.
        // FIXME: Using a semantics here prevents the function from inlining.
//        NewF->setSemanticsAttr("SharedSpec");
        NewF->setSharing(sharedF);
      //}
    }

    // TODO: Register this specialization
    registerSpecialization(M, F, NewF, Substitutions, SA);

    // Check if this specialization should be cached.
    cacheSpecialization(M, NewF);
  }

  // TODO: If NewF returns a different type than Apply, cast it into a proper type.
  if (F->getLoweredFunctionType()->isPolymorphic()) {
    CanSILFunctionType SubstFnTy =
        F->getLoweredFunctionType()->substGenericArgs(
            Apply.getModule(), Apply.getModule().getSwiftModule(),
            Apply.getSubstitutions());
    auto NewFnTy = dyn_cast<SILFunctionType>(NewF->getLoweredType().
                                                   getSwiftRValueType());
    if (SubstFnTy->getSILResult() != NewFnTy->getSILResult()) {
      llvm::dbgs() << "Return type needs to be adjusted\n";
    }
  }

  return replaceWithSpecializedFunction(Apply, NewF);
}
