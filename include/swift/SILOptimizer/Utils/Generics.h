//===--- Generics.h - Utilities for transforming generics -------*- C++ -*-===//
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
//
// This contains utilities for transforming generics.
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SIL_GENERICS_H
#define SWIFT_SIL_GENERICS_H

#include "swift/AST/Mangle.h"
#include "swift/SIL/Mangle.h"
#include "swift/SIL/SILFunction.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SILOptimizer/Utils/Local.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

namespace swift {

/// Tries to specialize an \p Apply of a generic function. It can be a full
/// apply site or a partial apply.
/// Replaced and now dead instructions are returned in \p DeadApplies.
/// New created functions, like the specialized callee and thunks, are returned
/// in \p NewFunctions.
///
/// This is the top-level entry point for specializing an existing call site.
void trySpecializeApplyOfGeneric(
    ApplySite Apply, DeadInstructionSet &DeadApplies,
    llvm::SmallVectorImpl<SILFunction *> &NewFunctions);

/// Helper class to describe re-abstraction of function parameters done during
/// specialization.
///
/// Specifically, it contains information which parameters and returns are
/// changed from indirect values to direct values.
class ReabstractionInfo {
  /// A 1-bit means that this parameter/return value is converted from indirect
  /// to direct.
  llvm::SmallBitVector Conversions;

  /// The first NumResults bits in Conversions refer to indirect out-parameters.
  unsigned NumResults;

  /// The function type after applying the substitutions of the original
  /// apply site.
  CanSILFunctionType SubstitutedType;

  /// The function type after applying the re-abstractions on the
  /// SubstitutedType.
  CanSILFunctionType SpecializedType;

  /// The generic environment to be used by the specialization.
  GenericEnvironment *SpecializedGenericEnv;

  /// The generic signature of the specializaiton.
  /// It is nullptr if the specialization is not polymorphic.
  GenericSignature *SpecializedGenSig;

  // Set of the original substitutions used by the caller's
  // apply instruction. It uses the contextual types of
  // the caller.
  ArrayRef<Substitution> ParamSubs;

  // Specialized set of substitutions to be used by the caller
  // when it calls a specialized function. It uses contextual
  // types of the caller.
  ArrayRef<Substitution> SpecializedParamSubs;

  // The adjusted set of substitutions for the caller's apply
  // instruction. It is for the original generic signature.
  // It uses the contextual types of the caller.
  // This set of substitutions is needed only for mangling,
  // if mangling uses a substitution-based approach for
  // encoding the specialized function's name.
  ArrayRef<Substitution> AdjustedParamSubs;

  // Adjusted set of substitutions to be used by the cloner.
  // It maps to the contextual types of the specialized function
  // being generated.
  ArrayRef<Substitution> AdjustedCloningParamSubs;

  // Map of substitutions used to create a new function type
  // for the specialized function. It maps to interface types
  // of the new generic environment.
  SubstitutionMap AdjustedInterfaceSubs;

  /// Create a new substituted type with the updated signature.
  CanSILFunctionType createSubstitutedType(SILFunction *OrigF,
                                           const TypeSubstitutionMap &SubstMap,
                                           bool HasUnboundGenericParams);

public:
  /// Constructs the ReabstractionInfo for generic function \p Orig with
  /// substitutions \p ParamSubs.
  /// If specialization is not possible getSpecializedType() will return an
  /// invalid type.
  ReabstractionInfo(SILFunction *Orig, ArrayRef<Substitution> ParamSubs);

  /// Does the \p ArgIdx refer to an indirect out-parameter?
  bool isResultIndex(unsigned ArgIdx) const {
    assert(ArgIdx < Conversions.size());
    return ArgIdx < NumResults;
  }

  /// Returns true if the \p ParamIdx'th (non-result) parameter is converted
  /// from indirect to direct.
  bool isParamConverted(unsigned ParamIdx) const {
    return Conversions.test(ParamIdx + NumResults);
  }

  /// Returns true if the \p ResultIdx'th result is converted from indirect
  /// to direct.
  bool isResultConverted(unsigned ResultIdx) const {
    assert(ResultIdx < NumResults);
    return Conversions.test(ResultIdx);
  }

  /// Gets the total number of original function arguments.
  unsigned getNumArguments() const { return Conversions.size(); }

  /// Returns true if the \p ArgIdx'th argument is converted from an indirect
  /// result or parameter to a direct result or parameter.
  bool isArgConverted(unsigned ArgIdx) const {
    return Conversions.test(ArgIdx);
  }

  /// Returns true if there are any conversions from indirect to direct values.
  bool hasConversions() const { return Conversions.any(); }

  /// Remove the arguments of a partial apply, leaving the arguments for the
  /// partial apply result function.
  void prunePartialApplyArgs(unsigned numPartialApplyArgs) {
    assert(numPartialApplyArgs <= Conversions.size());
    Conversions.resize(Conversions.size() - numPartialApplyArgs);
  }

  /// Returns the index of the first argument of an apply site, which may be
  /// > 0 in case of a partial_apply.
  unsigned getIndexOfFirstArg(ApplySite Apply) const {
    unsigned numArgs = Apply.getNumArguments();
    assert(numArgs == Conversions.size() || (numArgs < Conversions.size() &&
                                             isa<PartialApplyInst>(Apply)));
    return Conversions.size() - numArgs;
  }

  /// Get the function type after applying the substitutions to the original
  /// generic function.
  CanSILFunctionType getSubstitutedType() const { return SubstitutedType; }

  /// Get the function type after applying the re-abstractions on the
  /// substituted type. Returns an invalid type if specialization is not
  /// possible.
  CanSILFunctionType getSpecializedType() const { return SpecializedType; }

  GenericEnvironment *getSpecializedGenericEnvironment() const { return SpecializedGenericEnv; }

  ArrayRef<Substitution> getSpecializedParamSubstitutions() const { return SpecializedParamSubs; }

  ArrayRef<Substitution> getAdjustedParamSubstitutions() const { return AdjustedParamSubs; }

  ArrayRef<Substitution> getAdjustedCloningParamSubstitutions() const { return AdjustedCloningParamSubs; }

  const SubstitutionMap &getAdjustedInterfaceSubs() const { return AdjustedInterfaceSubs; }

  ArrayRef<Substitution> getParamSubstitutions() const { return ParamSubs; }

  /// Create a specialized function type for a specific substituted type \p
  /// SubstFTy by applying the re-abstractions.
  CanSILFunctionType createSpecializedType(CanSILFunctionType SubstFTy,
                                           SILModule &M) const;
};

/// Helper class for specializing a generic function given a list of
/// substitutions.
class GenericFuncSpecializer {
  SILModule &M;
  SILFunction *GenericFunc;
  ArrayRef<Substitution> ParamSubs;
  IsFragile_t Fragile;
  const ReabstractionInfo &ReInfo;

  SubstitutionMap ContextSubs;
  std::string ClonedName;
public:
  GenericFuncSpecializer(SILFunction *GenericFunc,
                         ArrayRef<Substitution> ParamSubs,
                         IsFragile_t Fragile,
                         const ReabstractionInfo &ReInfo);

  /// If we already have this specialization, reuse it.
  SILFunction *lookupSpecialization();

  /// Return a newly created specialized function.
  SILFunction *tryCreateSpecialization();
  
  /// Try to specialize GenericFunc given a list of ParamSubs.
  /// Returns either a new or existing specialized function, or nullptr.
  SILFunction *trySpecialization() {
    if (!ReInfo.getSpecializedType())
      return nullptr;

    SILFunction *SpecializedF = lookupSpecialization();
    if (!SpecializedF)
      SpecializedF = tryCreateSpecialization();

    return SpecializedF;
  }

  StringRef getClonedName() {
    return ClonedName;
  }
};

// =============================================================================
// Prespecialized symbol lookup.
// =============================================================================

/// Checks if a given mangled name could be a name of a whitelisted
/// specialization.
bool isWhitelistedSpecialization(StringRef SpecName);

/// Create a new apply based on an old one, but with a different
/// function being applied.
ApplySite replaceWithSpecializedFunction(ApplySite AI, SILFunction *NewF,
                                         const ReabstractionInfo &ReInfo);

/// Returns a SILFunction for the symbol specified by FunctioName if it is
/// visible to the current SILModule. This is used to link call sites to
/// externally defined specialization and should only be used when the function
/// body is not required for further optimization or inlining (-Onone).
SILFunction *lookupPrespecializedSymbol(SILModule &M, StringRef FunctionName);

} // end namespace swift

#endif
