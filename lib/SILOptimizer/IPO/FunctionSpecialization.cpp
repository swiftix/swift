//===--- FunctionSpecialization.cpp - Specialize for constant arguments ---===//
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

#define DEBUG_TYPE "function-specialization"
#include "swift/AST/GenericEnvironment.h"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SILOptimizer/Utils/Generics.h"
#include "swift/SILOptimizer/Utils/SpecializationMangler.h"
#include "swift/Demangling/Demangle.h"
#include "swift/SIL/SILCloner.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SIL/TypeSubstCloner.h"
#include "swift/SILOptimizer/Analysis/ColdBlockInfo.h"
#include "swift/SILOptimizer/Analysis/DominanceAnalysis.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "swift/SILOptimizer/Utils/Local.h"
#include "swift/SILOptimizer/Utils/PerformanceInlinerUtils.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/Debug.h"

using namespace swift;

STATISTIC(NumFunctionsSpecialized,
          "Number of functions specialized for constant arguments");

namespace {
/// Specializes functions for constant argument values.
/// TODO: In the future, it could be extended to handle arguments, where
/// some properties of those arguments are known, e.g. some inequalities between
/// arguments, relations between an argument and a constant (like X > 0 or
/// Y != nil), exact type of the argument, etc. In this case, the specialized
/// function can make use of this information and generate better code by
/// performing some optimizations.
class FunctionSpecialization : public SILFunctionTransform
{
public:
  void run() override;
  SILFunction *specializeFunction(ApplySite Apply, SILFunction *OrigF,
                                  ArrayRef<SILValue> ArgumentValues);

protected:
  bool optimizeApply(ApplySite Apply);
};
} // end anonymous namespace

/// Check if a value is a constant.
/// The most profitable case is when the value is a function reference.
/// But in principle, we can support any kind of literal instructions.
///
/// NOTE: We could even support any "constant value", which can be e.g.
/// a struct instruction and so on, similar to how we determine constant
/// values in let propagation passes.
/// The problem here is how to encode such a constant value in the mangled name
/// of a specialized function? May be we can simply compute the MD5 hash of
/// a string representing the set of instructions computing a constant value and
/// append this hash to the function name? If we go this way, we need to canonicalize
/// the set of instructions that we we emit as a string, so that e.g.
/// different SILValue IDs do not result in different string representations.
static LiteralInst *getConstant(SILValue V) {
  if (auto I = dyn_cast<ThinToThickFunctionInst>(V))
    return getConstant(I->getOperand());
  if (auto I = dyn_cast<ConvertFunctionInst>(V))
    return getConstant(I->getOperand());
  return dyn_cast<FunctionRefInst>(V);
}

static bool isOptimizableConstant(SILValue V) {
  // We do not optimize string literals of length > 32 since we would need to
  // encode them into the symbol name for uniqueness.
  if (auto *SLI = dyn_cast<StringLiteralInst>(V))
    return SLI->getValue().size() <= 32;
  return true;
}

static bool isConstant(SILValue V) {
  V = getConstant(V);
  return V && isOptimizableConstant(V);
}

static std::string getClonedName(ApplySite Apply, IsSerialized_t Serialized,
                                 SILFunction *F,
                                 ArrayRef<SILValue> ArgumentValues) {
  auto P = Demangle::SpecializationPass::FunctionSpecializer;
  Mangle::FunctionSignatureSpecializationMangler Mangler(P, Serialized, F);

  // We know that some arguments are literal insts.
  unsigned argIdx = Apply.getCalleeArgIndexOfFirstAppliedArg();
  for (auto arg : Apply.getArguments()) {
    auto argValue = ArgumentValues[argIdx];
    if (argValue)
      Mangler.setArgumentConstantProp(argIdx, getConstant(argValue));
    ++argIdx;
  }
  return Mangler.mangle();
}

namespace {
/// Clone the partially applied function, replacing incoming arguments with
/// literal constants.
///
/// The cloned literals will retain the SILLocation from the partial apply's
/// caller, so the cloned function will have a mix of locations from different
/// functions.
class FunctionSpecializationCloner
  : public TypeSubstCloner<FunctionSpecializationCloner> {
  using SuperTy = TypeSubstCloner<FunctionSpecializationCloner>;
  friend class SILVisitor<FunctionSpecializationCloner>;
  friend class SILCloner<FunctionSpecializationCloner>;

  // The function being cloned.
  SILFunction *OrigF;
  ArrayRef<SILValue> ArgumentValues;
  bool IsCloningConstant;
public:
  FunctionSpecializationCloner(SILFunction *OrigF,
                               ArrayRef<SILValue> ArgumentValues,
                               SILFunction *NewF, SubstitutionList Subs)
      : SuperTy(*NewF, *OrigF, Subs), OrigF(OrigF),
        ArgumentValues(ArgumentValues), IsCloningConstant(false) {}

  void cloneBlocks();

protected:
  /// Literals cloned from the caller drop their location so the debug line
  /// tables don't senselessly jump around. As a placeholder give them the
  /// location of the newly cloned function.
  SILLocation remapLocation(SILLocation InLoc) {
    if (IsCloningConstant)
      return getBuilder().getFunction().getLocation();
    return InLoc;
  }

  /// Literals cloned from the caller take on the new function's debug scope.
  void postProcess(SILInstruction *Orig, SILInstruction *Cloned) {
    // Check if it is a self-recursive call with a wrong number of arguments.
    // If this is the case, correct it by omitting the removed arguments.
    if (ApplySite Apply = ApplySite::isa(Cloned)) {
      auto RefF = Apply.getReferencedFunction();
      SILFunctionConventions conv = Cloned->getFunction()->getConventions();
      if (RefF == Cloned->getFunction() &&
          Apply.getNumCallArguments() != conv.getNumSILArguments()) {
        assert(ArgumentValues.size() == Apply.getArguments().size());
        // Create a proper list of arguments.
        auto ApplyArguments = Apply.getArguments();
        SmallVector<SILValue, 4> Arguments;
        unsigned ParamIdx = 0;
        for (auto Arg : ArgumentValues) {
          if (!Arg)
            Arguments.push_back(ApplyArguments[ParamIdx]);
          ParamIdx++;
        }
        assert(Arguments.size() == conv.getNumSILArguments());
        // Create a new apply instruction.
        if (auto *AI = dyn_cast<ApplyInst>(Cloned)) {
          doPostProcess(Orig,
                        Builder.createApply(AI->getLoc(), AI->getCallee(),
                                            AI->getSubstCalleeSILType(),
                                            AI->getType(),
                                            AI->getSubstitutions(), Arguments,
                                            AI->isNonThrowing()));
          Cloned->eraseFromParent();
          return;
        }

        if (auto *TAI = dyn_cast<TryApplyInst>(Cloned)) {
          doPostProcess(Orig,
                        Builder.createTryApply(TAI->getLoc(), TAI->getCallee(),
                                               TAI->getSubstCalleeSILType(),
                                               TAI->getSubstitutions(),
                                               Arguments, TAI->getNormalBB(),
                                               TAI->getErrorBB()));
          Cloned->eraseFromParent();
          return;
        }
        llvm_unreachable("Unsupported apply kind");
      }
    }

    SILClonerWithScopes<FunctionSpecializationCloner>::postProcess(Orig,
                                                                   Cloned);
  }

  const SILDebugScope *remapScope(const SILDebugScope *DS) {
    if (IsCloningConstant)
      return getBuilder().getFunction().getDebugScope();
    else
      return SILClonerWithScopes<FunctionSpecializationCloner>::remapScope(DS);
  }

  void cloneConstValue(SILValue Const);
};
} // end anonymous namespace

/// Clone a constant value. Recursively walk the operand chain through cast
/// instructions to ensure that all dependents are cloned. Note that the
/// original value may not belong to the same function as the one being cloned
/// by cloneBlocks() (they may be from the partial apply caller).
void FunctionSpecializationCloner::cloneConstValue(SILValue Val) {
  assert(IsCloningConstant && "incorrect mode");

  auto Inst = dyn_cast<SILInstruction>(Val);
  if (!Inst)
    return;

  auto II = InstructionMap.find(Inst);
  if (II != InstructionMap.end())
    return;

  if (Inst->getNumOperands() > 0) {
    // Only handle single operands for simple recursion without a worklist.
    assert(Inst->getNumOperands() == 1 && "expected single-operand cast");
    cloneConstValue(Inst->getOperand(0));
  }
  visit(Inst);
}

/// Clone the original callee function into the new specialized
/// function, replacing some arguments with literals.
void FunctionSpecializationCloner::cloneBlocks() {
  SILFunction &CloneF = getBuilder().getFunction();

  // Create the entry basic block with the function arguments.
  SILBasicBlock *OrigEntryBB = &*OrigF->begin();
  SILBasicBlock *ClonedEntryBB = CloneF.createBasicBlock();
  auto cloneConv = CloneF.getConventions();
  auto origConv = OrigF->getConventions();

  // Only clone the arguments that remain in the new function type. The trailing
  // arguments are now propagated through the partial apply.
  assert(!IsCloningConstant && "incorrect mode");
  unsigned ParamIdx = 0;
  for (unsigned NewParamEnd = origConv.getNumSILArguments();
       ParamIdx != NewParamEnd; ++ParamIdx) {

    // No need to introduce any function arguments for the arguments with
    // constant values.
    if (ArgumentValues[ParamIdx])
      continue;

    SILArgument *Arg = OrigEntryBB->getArgument(ParamIdx);

    SILValue MappedValue = ClonedEntryBB->createFunctionArgument(
        remapType(Arg->getType()), Arg->getDecl());
    ValueMap.insert(std::make_pair(Arg, MappedValue));
  }

  // Replace the rest of the old arguments with constants.
  BBMap.insert(std::make_pair(OrigEntryBB, ClonedEntryBB));
  getBuilder().setInsertionPoint(ClonedEntryBB);
  IsCloningConstant = true;

  ParamIdx = 0;
  for (unsigned NewParamEnd = origConv.getNumSILArguments();
       ParamIdx != NewParamEnd; ++ParamIdx) {

    auto Arg = ArgumentValues[ParamIdx];
    // Skip arguments that are still present in the new function.
    if (!Arg)
      continue;

    assert(isConstant(Arg) && "expected a constant arg to apply");

    cloneConstValue(Arg);

    // The arg from the caller is now mapped to its cloned
    // instruction.  Also map the original argument to the cloned instruction.
    SILArgument *InArg = OrigEntryBB->getArgument(ParamIdx);
    ValueMap.insert(std::make_pair(InArg, remapValue(Arg)));
  }

  IsCloningConstant = false;
  // Recursively visit original BBs in depth-first preorder, starting with the
  // entry block, cloning all instructions other than terminators.
  visitSILBasicBlock(OrigEntryBB);

  // Now iterate over the BBs and fix up the terminators.
  for (auto BI = BBMap.begin(), BE = BBMap.end(); BI != BE; ++BI) {
    getBuilder().setInsertionPoint(BI->second);
    visit(BI->first->getTerminator());
  }
}

/// Given an apply instruction, create a specialized callee by removing
/// all constant arguments and adding constant literals to the specialized
/// function body.
SILFunction *
FunctionSpecialization::specializeFunction(ApplySite Apply, SILFunction *OrigF,
                                           ArrayRef<SILValue> ArgumentValues) {
  IsSerialized_t Serialized = IsNotSerialized;
  if (Apply->getFunction()->isSerialized() && OrigF->isSerialized())
    Serialized = IsSerializable;

  std::string Name = getClonedName(Apply, Serialized, OrigF, ArgumentValues);

  // See if we already have a version of this function in the module. If so,
  // just return it.
  if (auto *NewF = OrigF->getModule().lookUpFunction(Name)) {
    assert(NewF->isSerialized() == Serialized);
    DEBUG(llvm::dbgs()
              << "  Found an already specialized version of the callee: ";
          NewF->printName(llvm::dbgs()); llvm::dbgs() << "\n");
    return NewF;
  }

  auto &M = OrigF->getModule();

  // Create the function type of a specialized function.
  auto FnTy = OrigF->getLoweredFunctionType();
  auto Parameters = FnTy->getParameters();
  auto OrigConv = OrigF->getConventions();
  SmallVector<SILParameterInfo, 4> NewParameters;
  assert(OrigConv.getNumSILArguments() == ArgumentValues.size());
  // Drop all constant parameters.
  unsigned ParamIdx = OrigConv.getSILArgIndexOfFirstParam();
  for (auto SILParamInfo : Parameters) {
    auto ArgValue = ArgumentValues[ParamIdx++];
    if (!ArgValue)
      NewParameters.push_back(SILParamInfo);
  }

  auto NewFnTy = SILFunctionType::get(
      FnTy->getGenericSignature(), FnTy->getExtInfo(),
      FnTy->getCalleeConvention(), NewParameters, FnTy->getResults(),
      FnTy->getOptionalErrorResult(), M.getASTContext());

  GenericEnvironment *GenericEnv = nullptr;
  if (NewFnTy->getGenericSignature())
    GenericEnv = OrigF->getGenericEnvironment();
  SILFunction *NewF = OrigF->getModule().createFunction(
      SILLinkage::Shared, Name, NewFnTy,
      GenericEnv, OrigF->getLocation(), OrigF->isBare(),
      OrigF->isTransparent(), Serialized, OrigF->isThunk(),
      OrigF->getClassSubclassScope(), OrigF->getInlineStrategy(),
      OrigF->getEffectsKind(),
      /*InsertBefore*/ OrigF, OrigF->getDebugScope());

  if (OrigF->hasUnqualifiedOwnership()) {
    NewF->setUnqualifiedOwnership();
  }
  DEBUG(llvm::dbgs() << "  Specialize callee as ";
        NewF->printName(llvm::dbgs()); llvm::dbgs() << " " << NewFnTy << "\n");

  DEBUG(if (Apply.hasSubstitutions()) {
    llvm::dbgs() << "FunctionSpecialization of generic apply:\n";
    Apply->dumpInContext();
  });
  FunctionSpecializationCloner cloner(OrigF, ArgumentValues, NewF,
                                      Apply.getSubstitutions());
  cloner.cloneBlocks();
  assert(OrigF->getDebugScope()->Parent != NewF->getDebugScope()->Parent);
  return NewF;
}

// TODO: Provide a more intelligent guess.
static bool isProfitable(SILFunction *Callee) {
  return true;
}

static bool cannotBeInlined(ApplySite Apply, SILFunction *F) {
  FullApplySite AI = FullApplySite(Apply.getInstruction());
  if (AI && !getEligibleFunction(AI, InlineSelection::Everything))
    return true;
  if (F->hasSemanticsAttr("function_specialization") ||
      Apply.getFunction()->hasSemanticsAttr("function_specialization"))
    return true;
  return false;
  //return F->getInlineStrategy() == NoInline;
}

bool FunctionSpecialization::optimizeApply(ApplySite Apply) {
  auto *SubstF = Apply.getReferencedFunction();
  if (!SubstF)
    return false;
  if (SubstF->isExternalDeclaration())
    return false;

  // Do not specialize functions that can be inlined, unless
  // they are called from a function specialized by this pass.
  // This is to ensure that we do not generate too many specialized
  // functions if we could have just inlined them.
  if (!cannotBeInlined(Apply, SubstF))
    return false;

  if (Apply.hasSubstitutions() && hasArchetypes(Apply.getSubstitutions())) {
    DEBUG(llvm::dbgs()
              << "FunctionSpecialization: cannot handle partial specialization "
                 "of apply sites:\n";
          Apply->dumpInContext());
    return false;
  }

  SmallVector<SILValue, 4> ArgumentValues;
  auto &M = Apply.getModule();
  // Check which arguments are constants.
  for (auto Arg : Apply.getArguments()) {
    if (!isConstant(Arg))
      ArgumentValues.push_back(SILValue());
    else
      ArgumentValues.push_back(Arg);
  }

  // Continue only if at least one argument is a constant.
  if (!llvm::any_of(ArgumentValues, [](SILValue v) -> bool { return v; }))
    return false;

  if (!isProfitable(SubstF))
    return false;

  DEBUG(llvm::dbgs() << "\n\nSpecializing function for constant arguments:\n"
                     << "  " << SubstF->getName() << "\n";
        Apply->dumpInContext();
        llvm::dbgs() << "Constant arguments are:\n";
        auto ParamIdx = 0;
        for (auto Arg : ArgumentValues) {
          if (Arg) {
            llvm::dbgs() << "Argument " << ParamIdx << ":";
            Arg->dumpInContext();
          }
          ++ParamIdx;
        }
        llvm::dbgs() << "\n");

  ++NumFunctionsSpecialized;
  SILFunction *NewF = specializeFunction(Apply, SubstF, ArgumentValues);
  DEBUG(llvm::dbgs() << "Created specialized function: " << NewF->getName()
                     << "\n");
  // Mark the new function as a specialization produced by this pass.
  NewF->addSemanticsAttr("function_specialization");
  auto NewConv = NewF->getConventions();

  // Update the old apply site to call the new specialized function.
  ReabstractionInfo ReInfo(Apply, NewF);
  for (unsigned ParamIdx = 0; ParamIdx < ArgumentValues.size(); ++ParamIdx) {
    if (ArgumentValues[ParamIdx])
      ReInfo.setParamDead(ParamIdx - NewConv.getSILArgIndexOfFirstParam());
  }
  replaceWithSpecializedFunction(Apply, NewF, ReInfo);
  recursivelyDeleteTriviallyDeadInstructions(Apply.getInstruction(), true);

  notifyAddFunction(NewF, SubstF);
  return true;
}

void FunctionSpecialization::run() {
  DominanceAnalysis *DA = PM->getAnalysis<DominanceAnalysis>();
  auto *F = getFunction();
  bool HasChanged = false;

  // Don't optimize functions that are excluded from optimization.
  if (!F->shouldOptimize())
    return;

  // Cache cold blocks per function.
  ColdBlockInfo ColdBlocks(DA);
  for (auto &BB : *F) {
    if (ColdBlocks.isCold(&BB))
      continue;

    auto I = BB.begin();
    while (I != BB.end()) {
      SILInstruction *Inst = &*I;
      ++I;
      if (auto Apply = FullApplySite::isa(Inst))
        HasChanged |= optimizeApply(Apply);
    }
  }

  if (HasChanged) {
    invalidateAnalysis(SILAnalysis::InvalidationKind::Everything);
  }
}

SILTransform *swift::createFunctionSpecialization() {
  return new FunctionSpecialization();
}
