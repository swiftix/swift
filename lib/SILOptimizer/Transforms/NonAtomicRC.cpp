//===-------  NonAtomicRC.cpp - Use non-atomic reference counting  -------===//
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

#define DEBUG_TYPE "non-atomic-rc"
#include "swift/SIL/InstructionUtils.h"
#include "swift/SIL/SILArgument.h"
#include "swift/SIL/SILBuilder.h"
#include "swift/SIL/SILCloner.h"
#include "swift/SILOptimizer/Analysis/ArraySemantic.h"
#include "swift/SILOptimizer/Analysis/DominanceAnalysis.h"
#include "swift/SILOptimizer/Analysis/EscapeAnalysis.h"
#include "swift/SILOptimizer/Analysis/RCIdentityAnalysis.h"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "swift/SILOptimizer/Utils/Generics.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"

STATISTIC(NumNonAtomicRC, "Number of non-atomic RC operations");

llvm::cl::opt<bool> PerformNonAtomicOpts(
    "non-atomic-opts", llvm::cl::init(true),
    llvm::cl::desc("Enable non-atomic reference counting optimizations"));

using namespace swift;

namespace {

// Bitvector implementation to be used for the dataflow analysis.
typedef llvm::SmallBitVector StateBitVector;

llvm::raw_ostream &operator<<(llvm::raw_ostream &stream, llvm::BitVector &BV) {
  unsigned size = BV.size();
  stream << "[ ";
  for (unsigned i = 0; i < size; ++i)
    stream << BV[i] << " ";
  stream << ']';
  return stream;
}

llvm::raw_ostream &operator<<(llvm::raw_ostream &stream,
                              llvm::SmallBitVector &BV) {
  unsigned size = BV.size();
  stream << "[ ";
  for (unsigned i = 0; i < size; ++i)
    stream << BV[i] << " ";
  stream << ']';
  return stream;
}

/// Representation of a BB state during the dataflow analysis.
/// Bit vectors are indexed by the id of a COW value.
struct BlockState {
  StateBitVector In;
  StateBitVector Out;
  StateBitVector Gen;
  StateBitVector Kill;
};

class Dataflow {
protected:
  SILFunction *F;

  // Maps a basic block to its numeric id
  llvm::DenseMap<SILBasicBlock *, int> BlockIds;

  // Dataflow analysis state for each BB.
  // Indexed by the ids assigned in BlockIds.
  std::vector<BlockState> BlockStates;

  // Bit verctor length used by the dataflow analysis.
  // It represents the number of different properties
  // being tracked.
  unsigned StateLength;

public:
  Dataflow(SILFunction *F);
  int getBlockIdx(SILBasicBlock *BB) const { return BlockIds.lookup(BB); }
  unsigned getStateLength() const { return StateLength; }
  void setStateLength(unsigned Length) {
    assert(!StateLength);
    StateLength = Length;
  }
  virtual void initStates();
  virtual StateBitVector mergePredecessorStates(SILBasicBlock *BB);
  virtual void compute();
  BlockState &getBlockState(SILBasicBlock *BB) {
    return BlockStates[BlockIds[BB]];
  }
  virtual void dump();
  virtual ~Dataflow() {}
};

Dataflow::Dataflow(SILFunction *F) : F(F), StateLength(0) {
  // Assign ids to each BB.
  unsigned idx = 0;
  for (auto &BB : *F) {
    BlockIds[&BB] = idx++;
  }

  // Reserve enough space for BB states.
  BlockStates.resize(BlockIds.size());
}

void Dataflow::initStates() {
  /*
    for (auto &BBState: BlockStates)  {
      // In is all 1s
      BBState.In.flip();
      // Out is all 0s
      BBState.Out.reset();
      // Gen is all 0s
      BBState.Gen.reset();
      // Kill is all 0s
      BBState.Kill.reset();
    }
  */
}

/// Perform a logical AND on the OUT sets of all predecessors.
StateBitVector Dataflow::mergePredecessorStates(SILBasicBlock *BB) {
  if (BB->pred_empty())
    return getBlockState(BB).In;
  StateBitVector Result(getStateLength(), true);
  for (auto Pred : BB->getPreds()) {
    Result &= getBlockState(Pred).Out;
  }
  return Result;
}

/// Main loop of the dataflow analysis.
void Dataflow::compute() {
  // TODO: Use a worklist for a faster convergence
  bool Changed;
  // Iterate until a fixpoint is reached.
  do {
    Changed = false;
    // Visit all BBs
    // TODO: Use a good order, so that definitions are always visited
    // before their uses.
    // Update the in/out sets.
    for (auto &BB : *F) {
      auto &BBState = getBlockState(&BB);
      auto NewIn = mergePredecessorStates(&BB);
      assert(NewIn.size() == getStateLength());
      if (!Changed && NewIn != BBState.In)
        Changed = true;
      BBState.In = NewIn;
      // Out = (NewIn &  ~Kill) | Gen
      // Gen should be added last, because you may have a kill and a gen
      // in the same basic block.
      auto NewOut = NewIn;
      assert(NewOut.size() == getStateLength());
      NewOut.reset(BBState.Kill);
      assert(NewOut.size() == getStateLength());
      NewOut |= BBState.Gen;
      assert(NewOut.size() == getStateLength());
      if (!Changed && BBState.Out != NewOut)
        Changed = true;
      BBState.Out = NewOut;
    }
  } while (Changed);
}

/// Helper function to dump the results of
/// the dataflow analysis.
void Dataflow::dump() {
  for (auto &BB : *F) {
    auto &BlockState = getBlockState(&BB);
    auto BBId = getBlockIdx(&BB);
    DEBUG(llvm::dbgs() << "\nDataflow results for BB " << BBId << ":\n";
          llvm::dbgs() << "In = " << BlockState.In << "\n";
          llvm::dbgs() << "Out = " << BlockState.Out << "\n";
          llvm::dbgs() << "Gen = " << BlockState.Gen << "\n";
          llvm::dbgs() << "Kill = " << BlockState.Kill << "\n"; BB.dump());
  }
}

// Customization of a general dataflow analysis
// for tracking the uniguqness.
class UniquenessDataflow : public Dataflow {
public:
  UniquenessDataflow(SILFunction *F) : Dataflow(F) {}

  void initStates(unsigned StateLength) {
    setStateLength(StateLength);

    for (auto &BBState : BlockStates) {
      BBState.In.resize(getStateLength(), false);
      BBState.Out.resize(getStateLength(), false);
      BBState.Gen.resize(getStateLength(), false);
      BBState.Kill.resize(getStateLength(), false);
    }

    // Entry block does not have any bits set for the In set.
    getBlockState(&*F->begin()).In.reset();
  }

  void compute() {
    Dataflow::compute();
    dump();
  }
};

typedef SILAnalysis::InvalidationKind StateChanges;

class NonAtomicRCTransformer {
  SILPassManager *PM;
  SILFunction *F;
  EscapeAnalysis::ConnectionGraph *ConGraph;
  EscapeAnalysis *EA;
  RCIdentityFunctionInfo *RCIFI;

  UniquenessDataflow DF;

  // Map the CowValue to the assigned id.
  llvm::DenseMap<SILValue, unsigned> CowValueId;

  // Map the assigned id to CowValue.
  llvm::SmallVector<SILValue, 32> IdToCowValue;

  // The set of instructions that are interesting for this
  // optimization.
  llvm::SmallPtrSet<SILInstruction *, 32> Candidates;

  // The set of basic blocks containing instructions
  // that are interesting for this optimization.
  llvm::SmallPtrSet<SILBasicBlock *, 32> CandidateBBs;
  unsigned UniqueIdx;

public:
  NonAtomicRCTransformer(SILPassManager *PM, SILFunction *F,
                         EscapeAnalysis::ConnectionGraph *ConGraph,
                         EscapeAnalysis *EA, RCIdentityFunctionInfo *RCIFI)
      : PM(PM), F(F), ConGraph(ConGraph), EA(EA), RCIFI(RCIFI), DF(F),
        UniqueIdx(0) {}

  StateChanges process();

private:
  StateChanges processUniqenessRegions();
  StateChanges processNonEscapingRefCountingInsts();
  bool isEligableRefCountingInst(SILInstruction *I);
  StateChanges tryNonAtomicRC(SILInstruction *I);
  bool isCowValue(ValueBase *CowStruct, SILValue Value);
  bool isRCofCowValueAt(ValueBase *CowStruct, SILInstruction *Inst);
  bool isStoreAliasingCowValue(ValueBase *CowStruct, SILValue Dest);
  void findAllMakeUnique();
  void findUniqueParameters();
  void scanAllBlocks();
  void scanBasicBlock(SILBasicBlock *BB);
  StateChanges transformAllBlocks();
  void getCowValueArgsOfApply(FullApplySite AI, SILValue CowValue,
                              SmallVectorImpl<int> &Args,
                              SmallVectorImpl<bool> &IsIndirectParam);
  void markAsCandidate(SILInstruction *I);
  void replaceByNonAtomicApply(FullApplySite AI);
  SILFunction *createNonAtomicFunction(SILFunction *F);
  bool isBeneficialToClone(SILFunction *F);
};

namespace {
/// \brief A SILCloner subclass which clones a closure function while
/// promoting some of its box parameters to stack addresses.
class FunctionCloner : public SILClonerWithScopes<FunctionCloner> {
public:
  friend class SILVisitor<FunctionCloner>;
  friend class SILCloner<FunctionCloner>;

  FunctionCloner(SILFunction *Orig, llvm::StringRef ClonedName);

  void populateCloned();

  SILFunction *getCloned() { return &getBuilder().getFunction(); }

private:
  static SILFunction *initCloned(SILFunction *Orig, llvm::StringRef ClonedName);

  SILFunction *Orig;
};
} // end anonymous namespace.

FunctionCloner::FunctionCloner(SILFunction *Orig, llvm::StringRef ClonedName)
    : SILClonerWithScopes<FunctionCloner>(*initCloned(Orig, ClonedName)),
      Orig(Orig) {
  assert(Orig->getDebugScope()->getParentFunction() !=
         getCloned()->getDebugScope()->getParentFunction());
}

/// \brief Create the function corresponding to the clone of the
/// original function.
SILFunction *FunctionCloner::initCloned(SILFunction *Orig,
                                        llvm::StringRef ClonedName) {
  SILModule &M = Orig->getModule();

  SmallVector<SILParameterInfo, 4> ClonedInterfaceArgTys;

  // Generate a new parameter list.
  auto OrigFTI = Orig->getLoweredFunctionType();

  // Create the new function type for the cloned function.
  auto ClonedTy = OrigFTI;

  assert((Orig->isTransparent() || Orig->isBare() || Orig->getLocation()) &&
         "SILFunction missing location");
  assert((Orig->isTransparent() || Orig->isBare() || Orig->getDebugScope()) &&
         "SILFunction missing DebugScope");
  assert(!Orig->isGlobalInit() && "Global initializer cannot be cloned");
  auto *Fn = M.getOrCreateFunction(
      SILLinkage::Shared, ClonedName, ClonedTy, Orig->getContextGenericParams(),
      Orig->getLocation(), Orig->isBare(), IsNotTransparent, Orig->isFragile(),
      Orig->isThunk(), Orig->getClassVisibility(), Orig->getInlineStrategy(),
      Orig->getEffectsKind(), Orig, Orig->getDebugScope());
  for (auto &Attr : Orig->getSemanticsAttrs()) {
    Fn->addSemanticsAttr(Attr);
  }
  Fn->setDeclCtx(Orig->getDeclContext());
  return Fn;
}

/// \brief Populate the body of the cloned closure, modifying instructions as
/// necessary to take into consideration the removed parameters.
void FunctionCloner::populateCloned() {
  SILFunction *Cloned = getCloned();
  SILModule &M = Cloned->getModule();

  // Create arguments for the entry block
  SILBasicBlock *OrigEntryBB = &*Orig->begin();
  SILBasicBlock *ClonedEntryBB = new (M) SILBasicBlock(Cloned);
  unsigned ArgNo = 0;
  auto I = OrigEntryBB->bbarg_begin(), E = OrigEntryBB->bbarg_end();
  while (I != E) {
    // Create a new argument which copies the original argument.
    SILValue MappedValue =
        new (M) SILArgument(ClonedEntryBB, (*I)->getType(), (*I)->getDecl());
    ValueMap.insert(std::make_pair(*I, MappedValue));
    ++I;
  }

  getBuilder().setInsertionPoint(ClonedEntryBB);
  BBMap.insert(std::make_pair(OrigEntryBB, ClonedEntryBB));
  // Recursively visit original BBs in depth-first preorder, starting with the
  // entry block, cloning all instructions other than terminators.
  visitSILBasicBlock(OrigEntryBB);

  // Now iterate over the BBs and fix up the terminators.
  for (auto BI = BBMap.begin(), BE = BBMap.end(); BI != BE; ++BI) {
    getBuilder().setInsertionPoint(BI->second);
    visit(BI->first->getTerminator());
  }
}

static SILFunction *getClonedFunction(SILFunction *OrigF, StringRef NewName) {
  FunctionCloner Cloner(OrigF, NewName);
  Cloner.populateCloned();
  return Cloner.getCloned();
}

static SILValue stripUniquenessPreservingCastsAndProjections(SILValue V) {
  while (V) {
    V = stripAddressProjections(V);
    V = stripCasts(V);
    if (auto *UAC = dyn_cast<UncheckedAddrCastInst>(V)) {
      if (UAC->getType() ==
          SILType::getNativeObjectType(UAC->getModule().getASTContext())
              .getAddressType()) {
        V = UAC->getOperand();
        continue;
      }
    }
    break;
  }
  return V;
}

// Create a version of the function which would use non-atomic
// reference counting for a given set of arguments.
SILFunction *NonAtomicRCTransformer::createNonAtomicFunction(SILFunction *F) {
  // TODO: Check if non-atomic version exists already and return
  // it if available.
  if (F->getName().endswith("_NonAtomic"))
    return F;
  // Otherwise clone and rewrite ref-counting operations in the body.
  SILModule &Mod = F->getModule();

  // Produce a mangled name of a non-atomic function.
  llvm::SmallString<128> MangledNonAtomicNameBuffer;
  llvm::raw_svector_ostream OS(MangledNonAtomicNameBuffer);
  OS << F->getName();
  OS << "_NonAtomic";
  StringRef MangledNonAtomicName = OS.str();
  auto *NewF = Mod.lookUpFunction(MangledNonAtomicName);
  if (NewF)
    return NewF;
  // if (Mod.hasFunction(MangledNonAtomicName, SILLinkage::Private))
  //  return Mod.lookUpFunction(MangledNonAtomicName);
  // Clone a function. Mark retain/releases as non-atomic.
  NewF = getClonedFunction(F, MangledNonAtomicName);
  // Remove the attribute.
  NewF->removeSemanticsAttr("generate.nonatomic");

  // Find all reference-counting instructions on Self argument or its
  // projections and make them non-atomic.
  // Fold all uniqueness checks of Self or its projections into true.
  // All calls of functions with @_semantics("generate.nonatomic") should
  // be replaced by the calls of their non-atomic versions.

  // TODO: Should it be done by the cloner?
  // To be on the safe side, we should compute the uniqueness regions and
  // stop the optimization at the instructions from a kill-set.
  // To do this, it is enough to assume that non-atomic arguments of the
  // functions are non-atomic at entry already.

  // The new non-atomic version should be processed by the same pass.
  // TODO: It would be nice, if the current function won't be reprocessed
  // again.
  DEBUG(llvm::dbgs() << "Schedule the newly created non-atomic function for "
                        "processing by non-atomic-opts pass: "
                     << NewF->getName() << "\n");
  PM->addFunctionToWorklist(NewF);
#if 0
  SILValue Self = NewF->getSelfArgument();
  for (auto &BB : *NewF) {
    auto II = BB.begin();
    while (II != BB.end()) {
      auto I = &*II++;

      // Do we need to track regions here and check for any
      // stores/calls that may overwrite Self?
      // Or do we assume that functions marked as generate.nonatomic
      // guarantee that Self remains unique after their execution?

      if (auto *RCI = dyn_cast<RefCountingInst>(I)) {
        // Get the RC root.
        auto Root = RCIFI->getRCIdentityRoot(
            stripAddressProjections(RCI->getOperand(0)));
        if (Root == Self)
          RCI->setNonAtomic(true);
        continue;
      }

      if (FullApplySite AI = FullApplySite::isa(I)) {
        auto Callee = AI.getCalleeFunction();
        // TODO: Check that the self argument if this call is
        // based on Self.
        if (Callee && Callee->hasSemanticsAttr("generate.nonatomic")) {
          // TODO: Can we run into endless recursion here?
          replaceByNonAtomicApply(AI);
        }
        continue;
      }

      // TODO: This peephole should be part of sil-combine, because
      // some of these instructions only become part of the
      // function after inlining.
      if (isa<IsUniqueInst>(I)) {
        SILValue Op = stripUniquenessPreservingCastsAndProjections(
          I->getOperand(0));
        auto Root = RCIFI->getRCIdentityRoot(Op);
        DEBUG(llvm::dbgs() << "Found is_unique: "; I->dump();
              llvm::dbgs() << "\n"
                           << "RCRoot = " << Root << "\n");
        if (Root != Self) {
          continue;
        }
        SILBuilderWithScope B(I);
        auto boolTy = SILType::getBuiltinIntegerType(1, Mod.getASTContext());
        auto yes = B.createIntegerLiteral(I->getLoc(), boolTy, 1);
        I->replaceAllUsesWith(yes);
        I->eraseFromParent();
        continue;
      }

      if (auto *BI = dyn_cast<BuiltinInst>(I)) {
        const BuiltinInfo &Builtin = BI->getBuiltinInfo();
        switch (Builtin.ID) {
        default:
          break;
        case BuiltinValueKind::IsUnique:
        case BuiltinValueKind::IsUniqueOrPinned:
        case BuiltinValueKind::IsUnique_native:
        case BuiltinValueKind::IsUniqueOrPinned_native:
          auto Root = RCIFI->getRCIdentityRoot(stripUniquenessPreservingCastsAndProjections(
              BI->getOperand(0)));
          if (Root != Self)
            break;
          // Replace this check by true.
          SILBuilderWithScope B(I);
          auto boolTy = SILType::getBuiltinIntegerType(1, Mod.getASTContext());
          auto yes = B.createIntegerLiteral(I->getLoc(), boolTy, 1);
          I->replaceAllUsesWith(yes);
          break;
        }
      }
    }
  }
#endif
  DEBUG(llvm::dbgs() << "Created a new non-atomic function: " << NewF->getName()
                     << "\n";
        NewF->dump());
  return NewF;
}

/// Check if it is beneficial to clone F if its
/// Self argument can be used non-atomically.
bool NonAtomicRCTransformer::isBeneficialToClone(SILFunction *F) {
  assert(F->hasSemanticsAttr("generate.nonatomic") &&
         "Only functions annotated with @_semantics(\"generate.nonatomic\") "
         "can be cloned");
  // If the function is marked as "generate.nonatomic", then it is supposed
  // to be cloned. Let's trust the developer for now.
  return true;
  SILValue Self = F->getSelfArgument();
  for (auto &BB : *F)
    for (auto &I : BB) {
      if (auto *RCI = dyn_cast<RefCountingInst>(&I)) {
        // Get the RC root.
        auto Root = RCIFI->getRCIdentityRoot(
            stripAddressProjections(RCI->getOperand(0)));
        if (Root == Self) {
          DEBUG(llvm::dbgs() << "Function is beneficial to clone becasue it "
                                "has RC instructions on its self argument");
          return true;
        }
      }
      // Check if there are any calls checking for uniqueness or having
      // non-atomic versions.
      ArraySemanticsCall Call(&I);
      if (Call && Call.hasSelf() &&
          RCIFI->getRCIdentityRoot(stripAddressProjections(Call.getSelf())) ==
              Self) {
        // This make mutable call can be folded, because it will be always true.
        if (Call.getKind() == ArrayCallKind::kMakeMutable)
          return true;
        FullApplySite AI = FullApplySite::isa(&I);
        if (AI &&
            AI.getCalleeFunction()->hasSemanticsAttr("generate.nonatomic"))
          return true;
      }
    }
  return false;
}

// Create a new apply based on an old one, but with a different
// function being applied.
// TODO: Make it a utility function.
static ApplySite replaceWithDifferentFunction(ApplySite AI, SILFunction *NewF) {
  assert(AI.getReferencedFunction()->getLoweredFunctionType() ==
             NewF->getLoweredFunctionType() &&
         "Types of functions should be exactly the same");
  SILBuilderWithScope Builder(AI.getInstruction());
  FunctionRefInst *Callee = Builder.createFunctionRef(AI.getLoc(), NewF);
  SILLocation Loc = AI.getLoc();
  SmallVector<SILValue, 4> Arguments;

  for (auto &Op : AI.getArgumentOperands()) {
    Arguments.push_back(Op.get());
  }

  if (auto *TAI = dyn_cast<TryApplyInst>(AI)) {
    SILBasicBlock *ResultBB = TAI->getNormalBB();
    assert(ResultBB->getSinglePredecessor() == TAI->getParent());
    auto *NewTAI = Builder.createTryApply(
        Loc, Callee, AI.getSubstCalleeSILType(), AI.getSubstitutions(),
        Arguments, ResultBB, TAI->getErrorBB());
    return NewTAI;
  }
  if (auto *A = dyn_cast<ApplyInst>(AI)) {
    auto ResultType = NewF->getLoweredType().getFunctionInterfaceResultType();
    auto *NewAI = Builder.createApply(Loc, Callee, AI.getSubstCalleeSILType(),
                                      ResultType, AI.getSubstitutions(),
                                      Arguments, A->isNonThrowing());
    A->replaceAllUsesWith(NewAI);
    return NewAI;
  }
  if (auto *PAI = dyn_cast<PartialApplyInst>(AI)) {
    auto *NewPAI = Builder.createPartialApply(
        Loc, Callee, AI.getSubstCalleeSILType(), AI.getSubstitutions(),
        Arguments,
        // AI.getOrigCalleeType()
        NewF->getLoweredType().getFunctionInterfaceResultType());
    PAI->replaceAllUsesWith(NewPAI);
    return NewPAI;
  }
  llvm_unreachable("unhandled kind of apply");
}

// Replace an atomic call by the non-atomic version
// of the call.
void NonAtomicRCTransformer::replaceByNonAtomicApply(FullApplySite AI) {
  auto *OrigCallee = AI.getCalleeFunction();
  if (!OrigCallee)
    return;
  if (!isBeneficialToClone(OrigCallee))
    return;
  auto *NewCallee = createNonAtomicFunction(OrigCallee);
  if (OrigCallee == NewCallee)
    return;
  FullApplySite NewApply;
  auto NewAI = replaceWithDifferentFunction(AI, NewCallee);
  AI.getInstruction()->replaceAllUsesWith(NewAI.getInstruction());
  recursivelyDeleteTriviallyDeadInstructions(AI.getInstruction(), true);
}

static void markAsNonAtomic(RefCountingInst *I) {
  SILValue Op = I->getOperand(0);
#if 0
  if (Op->getType() ==
      SILType::getBridgeObjectType(I->getModule().getASTContext())) {
    // Convert this bridged object to a native object ref.
    SILBuilder B(I);
    SILValue NativeRef = B.createBridgeObjectToRef(
        I->getLoc(), Op,
        SILType::getNativeObjectType(I->getModule().getASTContext()));
    RefCountingInst *NewI = nullptr;
    switch (I->getKind()) {
    default:
      llvm_unreachable("This reference counting instruction is not supported");
    case ValueKind::StrongRetainInst:
      NewI = B.createStrongRetain(I->getLoc(), NativeRef);
      break;
    case ValueKind::StrongReleaseInst:
      NewI = B.createStrongRelease(I->getLoc(), NativeRef);
      break;
    case ValueKind::StrongPinInst:
      NewI = B.createStrongPin(I->getLoc(), NativeRef);
      break;
    case ValueKind::StrongUnpinInst:
      NewI = B.createStrongUnpin(I->getLoc(), NativeRef);
      break;
    }
    NewI->setNonAtomic(true);
    I->replaceAllUsesWith(NewI);
    I->eraseFromParent();
    return;
  }
#endif
  I->setNonAtomic(true);
}

/// Returns true, if a given array semantics call does not
/// change the uniqueness of the array buffer.
static bool doesNotChangeUniquness(ArraySemanticsCall &C) {
  switch (C.getKind()) {
  default:
    return false;
  case ArrayCallKind::kArrayPropsIsNativeTypeChecked:
  case ArrayCallKind::kCheckSubscript:
  case ArrayCallKind::kCheckIndex:
  case ArrayCallKind::kGetCount:
  case ArrayCallKind::kGetCapacity:
  case ArrayCallKind::kGetElement:
  case ArrayCallKind::kGetArrayOwner:
  case ArrayCallKind::kGetElementAddress:
    return true;
  }
}

/// Is it a reference counting instruction that is eligable to
/// be promoted to a non-atomic version?
bool NonAtomicRCTransformer::isEligableRefCountingInst(SILInstruction *I) {
  return isa<RefCountingInst>(I) && !cast<RefCountingInst>(I)->isNonAtomic();
}

/// Try to promote a reference counting instruction to its non-atomic
/// variant.
StateChanges NonAtomicRCTransformer::tryNonAtomicRC(SILInstruction *I) {
  assert(isa<RefCountingInst>(I));
  auto *RCInst = cast<RefCountingInst>(I);
  auto Root = stripAddressProjections(RCInst->getOperand(0));
  auto *Node = ConGraph->getNodeOrNull(RCInst->getOperand(0), EA);
  if (!Node)
    return SILAnalysis::InvalidationKind::Nothing;

  // As long as the value does not escape the function, it is fine.
  if (Node->escapesInsideFunction(false))
    return SILAnalysis::InvalidationKind::Nothing;

  // This value does not escape, which means that it is
  // thread-local.
  // Use non-atomic RC instructions for it.
  markAsNonAtomic(RCInst);
  NumNonAtomicRC++;
  DEBUG(llvm::dbgs() << "Marking the RC instruction as non-atomic:\n";
        RCInst->dumpInContext(););
  return SILAnalysis::InvalidationKind::Instructions;
}

/// Is it an instruction that creates a uniquelly referenced
/// object?
static ArraySemanticsCall isMakeUniqueCall(SILInstruction *I) {
  ArraySemanticsCall Call(I);
  if (Call) {
    switch (Call.getKind()) {
    default:
      break;
    case ArrayCallKind::kMakeMutable:
    case ArrayCallKind::kMutateUnknown:
    case ArrayCallKind::kGuaranteeMutable:
      return Call;
    }
  }
  // TODO: Handle other COW types here?
  return ArraySemanticsCall(I, "non-existing", false);
}

/// \return true of the given container is known to be a unique copy of the
/// array with no aliases. Cases we check:
///
/// (1) An @inout argument.
///
/// (2) A local variable, which may be copied from a by-val argument,
/// initialized directly, or copied from a function return value. We don't
/// need to check how it is initialized here, because that will show up as a
/// store to the local's address.
bool checkUniqueCowContainer(SILFunction *Function, SILValue CowContainer) {
  if (SILArgument *Arg = dyn_cast<SILArgument>(CowContainer)) {
    // Check that the argument is passed as an inout type. This means there are
    // no aliases accessible within this function scope.
    auto Params = Function->getLoweredFunctionType()->getParameters();
    ArrayRef<SILArgument *> FunctionArgs = Function->begin()->getBBArgs();
    for (unsigned ArgIdx = 0, ArgEnd = Params.size(); ArgIdx != ArgEnd;
         ++ArgIdx) {
      if (FunctionArgs[ArgIdx] != Arg)
        continue;

      if (!Params[ArgIdx].isIndirectInOut()) {
        DEBUG(llvm::dbgs() << "    Skipping COW: Not an inout argument!\n";
              CowContainer->dump());
        return false;
      }
    }
    return true;
  }

  if (isa<AllocStackInst>(CowContainer))
    return true;

  DEBUG(llvm::dbgs()
            << "    Skipping COW object: Not an argument or local variable!\n";
        CowContainer->dump());
  return false;
}

bool NonAtomicRCTransformer::isCowValue(ValueBase *CowStruct, SILValue Value) {
  auto Root = RCIFI->getRCIdentityRoot(Value);
  if (Root == CowStruct)
    return true;
  auto *CowLoad = dyn_cast<LoadInst>(Root);
  if (!CowLoad)
    return false;

  if (CowLoad->getOperand() == CowStruct)
    return true;

  // Is it an RC operation on the buffer reference?
  if (RCIFI->getRCIdentityRoot(
          stripAddressProjections(CowLoad->getOperand())) == CowStruct)
    return true;

  return false;
}

/// Check that the array value stored in \p CowStruct is operand of this RC by
/// \Inst.
/// TODO: Support other COW types, not only array.
bool NonAtomicRCTransformer::isRCofCowValueAt(ValueBase *CowStruct,
                                              SILInstruction *Inst) {
  auto *RCI = dyn_cast<RefCountingInst>(Inst);
  if (!RCI)
    return false;
  if (isCowValue(CowStruct, RCI->getOperand(0)))
    return true;
  // Check if this is the "array.owner" of the array.
  SILValue Op = RCI->getOperand(0);
  ArraySemanticsCall Call(Op);
  if (!Call)
    return false;
  if (Call.getKind() != ArrayCallKind::kGetArrayOwner)
    return false;
  if (isCowValue(CowStruct, Call.getSelf()))
    return true;
  return false;
}

// TODO: Generalize for any COW types, not only arrays.
bool NonAtomicRCTransformer::isStoreAliasingCowValue(ValueBase *CowStruct,
                                                     SILValue Dest) {
  auto Root = RCIFI->getRCIdentityRoot(Dest);

  // Is it overwriting the array struct?
  if (Root == CowStruct)
    return true;

  // Is it a store to a field of a COW struct, e.g. to the buffer reference?
  // TODO: Make this check more precise?
  if (RCIFI->getRCIdentityRoot(stripAddressProjections(Root)) == CowStruct)
    return true;

  return false;
}

void NonAtomicRCTransformer::scanAllBlocks() {
  // Unique/non-atomic function parameters are in
  // the IN set of the entry block.
  for (auto Arg : F->getArguments()) {
    if (CowValueId.count(Arg)) {
      auto Id = CowValueId[Arg];
      DF.getBlockState(&*F->begin()).In[Id] = true;
    }
  }

  for (auto &BB : *F) {
    scanBasicBlock(&BB);
  }
}

void NonAtomicRCTransformer::getCowValueArgsOfApply(
    FullApplySite AI, SILValue CowValue, SmallVectorImpl<int> &Args,
    SmallVectorImpl<bool> &IsIndirectParam) {
  for (unsigned i = 0, e = AI.getArguments().size(); i < e; ++i) {
    auto Arg = AI.getArgument(i);
    if (isCowValue(CowValue, Arg))
      Args.push_back(i);
    else
      Args.push_back(-1); // -1 means that argument is not aliasing CowValue.
  }
  if (Args.empty())
    return;
  auto FnTy = AI.getSubstCalleeType();

  for (auto ResultInfo : FnTy->getIndirectResults()) {
    IsIndirectParam.push_back(ResultInfo.isIndirect());
  }

  for (auto ParamInfo : FnTy->getParameters()) {
    IsIndirectParam.push_back(ParamInfo.isIndirect());
  }
  assert(Args.size() == IsIndirectParam.size());
}

void NonAtomicRCTransformer::markAsCandidate(SILInstruction *I) {
  Candidates.insert(I);
  CandidateBBs.insert(I->getParent());
  DEBUG(llvm::dbgs() << "Mark as canidate:\n"; I->dumpInContext());
}

static bool isMakeOrGuaranteeMutable(ArraySemanticsCall &ArrayCall) {
  if (ArrayCall) {
    switch (ArrayCall.getKind()) {
    default:
      return false;
    case ArrayCallKind::kMakeMutable:
    case ArrayCallKind::kMutateUnknown:
    case ArrayCallKind::kGuaranteeMutable:
      return true;
    }
  }
  return false;
}

// Scan a basic block. Find all the "kill" instructions
// which may kill one of the CowValues being tracked.
// If there are any CowValues that become unique and then
// non-unique again inside the same BB, we don't want to
// account for that inside the dataflow analysis.
// If the last seen thing for a given CowValue is makeUnique
// then the Gen bit should be set.
// If the last thing seen is the Kill of a given CowValue,
// its Kill Set should be set.
//
// During the scan, remember the "interesting" instructions so
// that anything else can be skipped during the transformation stage.
void NonAtomicRCTransformer::scanBasicBlock(SILBasicBlock *BB) {
  // Remember if the last thing for a given CowValue
  // was kill or set.
  // Maps the CowValue to the last seen operation,
  // which is either set or kill.
  //
  enum Op { None, Gen, Kill };

  llvm::SmallVector<Op, 32> LastSeenOp;
  LastSeenOp.resize(DF.getStateLength());

  // Remember which CowValue regions were killed in this BB.
  StateBitVector KilledCowValues;
  KilledCowValues.resize(DF.getStateLength());

  auto II = BB->begin();
  while (II != BB->end()) {
    auto I = &*II++;

    // TODO: Generalize for any COW types, not only arrays.
    // Check if instruction may overwrite the array buffer reference in the
    // container.
    if (auto *SI = dyn_cast<StoreInst>(I)) {
      bool isAliasingDest = false;
      // Check if this instruction may store into a memory location
      // aliasing the location where array buffer reference is stored.
      auto Dest = SI->getDest();

      // Check if it kills any non-local region.
      for (auto &KV : CowValueId) {
        auto CowValue = KV.getFirst();
        auto Id = KV.getSecond();
        if (isStoreAliasingCowValue(CowValue, Dest)) {
          // This is a kill.
          LastSeenOp[Id] = Kill;
          KilledCowValues[Id] = true;
          isAliasingDest = true;
          markAsCandidate(I);
          DEBUG(llvm::dbgs() << "Kill operation for CowValue\n"
                             << CowValue;
                I->dumpInContext());
          break;
        }
      }
      if (isAliasingDest)
        continue;

      // Check if this instruction may store one of the tracked CowValues
      // somewhere. In this case, the buffer becomes non-unique.
      auto Src = SI->getSrc();
      for (auto &KV : CowValueId) {
        auto CowValue = KV.getFirst();
        auto Id = KV.getSecond();
        if (isCowValue(CowValue, Src)) {
          // This is a kill.
          LastSeenOp[Id] = Kill;
          KilledCowValues[Id] = true;
          markAsCandidate(I);
          DEBUG(llvm::dbgs() << "Kill operation for CowValue\n"
                             << CowValue;
                I->dumpInContext());
          break;
        }
      }
      continue;
    }

    if (auto AI = FullApplySite::isa(I)) {
      ArraySemanticsCall ArrayCall(AI.getInstruction());
      if (isMakeOrGuaranteeMutable(ArrayCall)) {
        // This is a GEN operation, it starts a region.
        auto CowValue = ArrayCall.getSelf();
        LastSeenOp[CowValueId[CowValue]] = Gen;
        markAsCandidate(I);

        DEBUG(llvm::dbgs() << "Gen operation for CowValue\n"
                           << CowValue;
              I->dumpInContext());

        continue;
      }

      // Check if this array semantics call takes one of the tracked
      // CowValues as its arguments.
      if (ArrayCall) {
        if (ArrayCall.getKind() ==
            ArrayCallKind::kArrayPropsIsNativeTypeChecked)
          markAsCandidate(I);
        if (doesNotChangeUniquness(ArrayCall))
          continue;

#if 1
        // Check whose uniqueness is changed.
        for (auto &KV : CowValueId) {
          auto CowValue = KV.getFirst();
          auto Id = KV.getSecond();
          SmallVector<int, 8> Args;
          SmallVector<bool, 8> IsIndirectParam;
          getCowValueArgsOfApply(AI, CowValue, Args, IsIndirectParam);
          if (Args.size()) {
            DEBUG(llvm::dbgs() << "Kill operation for CowValue:\n"
                               << CowValue;
                  I->dumpInContext());
            LastSeenOp[Id] = Kill;
            markAsCandidate(I);
            break;
          }
        }
#endif
        continue;
      }

      // Can this call escape the array container or array buffer reference?
      // TODO: Ask Erik how to query the EA in a proper way. We need to know
      // if the provided value can REALLY escape inside the function being
      // called.
      // Specifically, even if it is passed as "inout" parameter.
      // If it can be overwritten in the function, then it essentially
      // equivalent
      // to a store to the array and thus ends the region.
      // If it escapes inside the function, it also ends the region.
      // But what if it is only read inside the function? it would be nice if EA
      // would say it does not escape.

      // Check if it kills any non-local region.
      for (auto &KV : CowValueId) {
        auto CowValue = KV.getFirst();
        auto Id = KV.getSecond();
        SmallVector<int, 8> Args;
        SmallVector<bool, 4> IsIndirectParam;

        getCowValueArgsOfApply(AI, CowValue, Args, IsIndirectParam);
        if (Args.empty())
          continue;
        for (auto Arg : Args) {
          if (Arg < 0)
            continue;
          auto isIndirect = IsIndirectParam[Arg];
          if (EA->canParameterEscape(AI, Arg, isIndirect)) {
            LastSeenOp[Id] = Kill;
            KilledCowValues[Id] = true;
            markAsCandidate(I);
            DEBUG(llvm::dbgs() << "Kill operation for CowValue:\n"
                               << CowValue;
                  I->dumpInContext());
            break;
          }
        }
      }
      continue;
    }

    if (auto *DSI = dyn_cast<DeallocStackInst>(I)) {
      auto Val = DSI->getOperand();

      // Check if it kills any non-local region.
      for (auto &KV : CowValueId) {
        auto CowValue = KV.getFirst();
        auto Id = KV.getSecond();
        if (Val == CowValue) {
          // This is a kill.
          LastSeenOp[Id] = Kill;
          KilledCowValues[Id] = true;
          markAsCandidate(I);
          DEBUG(llvm::dbgs() << "Kill operation for CowValue\n"
                             << CowValue;
                I->dumpInContext());
          break;
        }
      }
      continue;
    }

    if (isa<IsUniqueInst>(I))
      markAsCandidate(I);

    if (isa<RefCountingInst>(I))
      markAsCandidate(I);

#if 0
    if (isa<StrongRetainInst>(I) || isa<RetainValueInst>(I)) {
      auto *RCI = cast<RefCountingInst>(I);
      SILValue RCVal = RCI->getOperand(0);
      // Check if this is a retain of the buffer.
      // If so, it makes it non-unique and thus kills the region.
      // Question: It may be non-unique, but it is still thread safe?
      for (auto &KV : CowValueId) {
        auto CowValue = KV.getFirst();
        auto Id = KV.getSecond();
        if (isArrayValue(CowValue, RCVal)) {
          // This is a kill.
          LastSeenOp[Id] = Kill;
          KilledCowValues[Id] = true;
          isAliasingDest = true;
          DEBUG(llvm::dbgs() << "Kill operation for CowValue\n" << CowValue;
                I->dumpInContext());
          break;
        }
      }
      continue;
    }
#endif

    // Nothing else can change or escape the array buffer reference.
    continue;
  }

  auto BBState = DF.getBlockState(BB);

  for (unsigned i = 0, e = LastSeenOp.size(); i < e; ++i) {
    if (LastSeenOp[i] == Gen)
      DF.getBlockState(BB).Gen[i] = true;
  }

  for (auto i = KilledCowValues.find_first(); i != -1;
       i = KilledCowValues.find_next(i)) {
    DF.getBlockState(BB).Kill[i] = true;
  }
}

// Use collected information about uniqueness regions to
// transform all basic blocks.
// Transformations include:
// - removal of redundant uniqueness checks
// - use of non-atomic versions of reference-counting instructions when
//   appropriate
// - use of non-atomic versions of functions which support non-atomic
//   invocations.
StateChanges NonAtomicRCTransformer::transformAllBlocks() {
  StateChanges Changes = SILAnalysis::InvalidationKind::Nothing;
  for (auto &BB : *F) {
    // Skip a BB if it does not contain any interesting instructions.
    if (!CandidateBBs.count(&BB))
      continue;

    auto &BBState = DF.getBlockState(&BB);
    // The set of currently active uniqness regions.
    // Indexed by the id of a CowValue being tracked.
    // Initialized with the IN set.
    StateBitVector CurrentlyActive(BBState.In);

    auto II = BB.begin();
    while (II != BB.end()) {
      auto I = &*II++;

      // If this instruction is not marked as "interesting" during the scan
      // phase, bail.
      if (!Candidates.count(I))
        continue;

      if (auto *RC = dyn_cast<RefCountingInst>(I)) {
        auto Ref = RC->getOperand(0);
        // If the region for a given CowValue is active and
        // if this is the array buffer reference or if this is
        // the array container itself, then it can be replaced
        // by a non-atomic variant.
        for (auto &KV : CowValueId) {
          auto CowValue = KV.getFirst();
          auto Id = KV.getSecond();
          // Check if it kills any non-local region.
          if (CurrentlyActive.test(Id) && isRCofCowValueAt(CowValue, I)) {
            Changes = StateChanges(Changes |
                                   SILAnalysis::InvalidationKind::Instructions);
            markAsNonAtomic(RC);
            DEBUG(llvm::dbgs()
                      << "RC operation inside make_mutable region can be "
                         "non-atomic: ";
                  RC->dump());
            break;
          }
        }
      }

      // Check if instruction may overwrite the array buffer reference in the
      // container.
      if (auto *SI = dyn_cast<StoreInst>(I)) {
        bool isAliasingDest = false;

        // Check if this instruction may store into a memory location
        // aliasing the location where array buffer reference is stored.
        auto Dest = SI->getDest();

        // Check if it kills any non-local region.
        for (auto &KV : CowValueId) {
          auto CowValue = KV.getFirst();
          auto Id = KV.getSecond();
          if (isStoreAliasingCowValue(CowValue, Dest)) {
            DEBUG(llvm::dbgs() << "Kill operation for CowValue\n"
                               << CowValue;
                  I->dumpInContext());
            // The region is not active anymore after this point.
            CurrentlyActive[Id] = false;
            isAliasingDest = true;
            break;
          }
        }
        if (isAliasingDest)
          continue;

        // Check if this instruction may store one of the tracked CowValues
        // somewhere. In this case, the buffer becomes non-unique.
        auto Src = SI->getSrc();
        for (auto &KV : CowValueId) {
          auto CowValue = KV.getFirst();
          auto Id = KV.getSecond();
          if (isCowValue(CowValue, Src)) {
            // This is a kill.
            CurrentlyActive[Id] = false;
            DEBUG(llvm::dbgs() << "Kill operation for CowValue\n"
                               << CowValue;
                  I->dumpInContext());
            break;
          }
        }
        continue;
      }

      if (auto AI = FullApplySite::isa(I)) {
        ArraySemanticsCall ArrayCall(AI.getInstruction());
        if (ArrayCall &&
            (ArrayCall.getKind() == ArrayCallKind::kGuaranteeMutable ||
             ArrayCall.getKind() == ArrayCallKind::kMutateUnknown)) {
          // TODO: Call a non-atomic version of the function?
          // The COW object that is made a thread-local by this call.
          auto CowValue = ArrayCall.getSelf();
          auto Id = CowValueId[CowValue];
          auto *Callee = AI.getCalleeFunction();

          if (CurrentlyActive.test(Id) &&
              Callee->hasSemanticsAttr("generate.nonatomic")) {
            DEBUG(llvm::dbgs()
                      << "Non-atomic version of the call can be used:\n";
                  AI.getInstruction()->dumpInContext());
            replaceByNonAtomicApply(AI);
          }
          // Mark region as active.
          CurrentlyActive[Id] = true;
          continue;
        }

        if (ArrayCall && ArrayCall.getKind() == ArrayCallKind::kMakeMutable) {
          // Add to the set of makeUnique calls
          // The COW object that is made a thread-local by this call.
          auto CowValue = ArrayCall.getSelf();

          // Check if this make_mutable is inside an existing region for the
          // same CowValue. If this is the case, then it can be removed.
          // The region may have started either in this BB or outside.
          // TODO: It can be that make_mutable is not only making something
          // mutable
          // but does more. In this case it cannot be removed.
          auto Id = CowValueId[CowValue];
          if (CurrentlyActive.test(Id)) {
            DEBUG(llvm::dbgs() << "make_mutable call can be eliminated:\n";
                  (*ArrayCall).dumpInContext());
            ArrayCall.removeCall();
            Changes =
                StateChanges(Changes | SILAnalysis::InvalidationKind::Calls);
            // TODO: Rescan the release instruction?
            continue;
          }

          // Mark region as active.
          CurrentlyActive[Id] = true;
          continue;
        }

        if (ArrayCall &&
            ArrayCall.getKind() ==
                ArrayCallKind::kArrayPropsIsNativeTypeChecked) {
#if 0
          auto CowValue = ArrayCall.getKindetSelf();
          // Check if this is_native_typecheck is inside an existing region for
          // the
          // same CowValue. If this is the case, then it can be removed, because
          // the buffer is always native after a make_mutable call.
          // The region may have started either in this BB or outside.
          auto Id = CowValueId[CowValue];
          if (CurrentlyActive.test(Id) && isArrayOfPods(CowValue)) {
            DEBUG(llvm::dbgs()
                      << "is_native_typecheck call can be eliminated:\n";
                  (*ArrayCall).dumpInContext());
            SILBuilder B(I);
            auto TrueVal = B.createIntegerLiteral(I->getLoc(),
                                   SILType::getBuiltinIntegerType(
                                       1, I->getModule().getASTContext()),
                                   -1);
            ArrayCall.replaceByValue(SILValue(TrueVal));
            Changes =
                StateChanges(Changes | SILAnalysis::InvalidationKind::Calls);
            // TODO: Rescan the release instruction?
            continue;
          }
#endif
        }

        // If this is a call of a method on the currently
        // unique COW object and this method has a non-atomic
        // verison, then this non-atomic version could be
        // used.
        if (AI.hasSelfArgument()) {
          auto *Callee = AI.getCalleeFunction();
          auto Self = AI.getSelfArgument();
          // Check if Self is currently unique.
          if (CowValueId.count(Self) > 0 &&
              CurrentlyActive.test(CowValueId[Self]) &&
              Callee->hasSemanticsAttr("generate.nonatomic")) {
            DEBUG(llvm::dbgs()
                      << "Non-atomic version of the call can be used:\n";
                  AI.getInstruction()->dumpInContext());
            replaceByNonAtomicApply(AI);
          }
        }

        if (ArrayCall) {
          if (doesNotChangeUniquness(ArrayCall))
            continue;
          // Check whose uniqueness is changed.
          for (auto &KV : CowValueId) {
            auto CowValue = KV.getFirst();
            auto Id = KV.getSecond();
            SmallVector<int, 8> Args;
            SmallVector<bool, 8> IsIndirectParam;
            getCowValueArgsOfApply(AI, CowValue, Args, IsIndirectParam);
            if (Args.size()) {
              CurrentlyActive[Id] = false;
              break;
            }
          }
          continue;
        }

        // TODO: If it is a semantics call, then we know it cannot
        // change the uniqueness.

        // Can this call escape the array container or array buffer reference?
        // TODO: Ask Erik how to query the EA in a proper way. We need to know
        // if the provided value can REALLY escape inside the function being
        // called.
        // Specifically, even if it is passed as "inout" parameter.
        // If it can be overwritten in the function, then it essentially
        // equivalent
        // to a store to the array and thus ends the region.
        // If it escapes inside the function, it also ends the region.
        // But what if it is only read inside the function? it would be nice if
        // EA
        // would say it does not escape.

        // Check if it kills any non-local region.
        for (auto &KV : CowValueId) {
          auto CowValue = KV.getFirst();
          auto Id = KV.getSecond();
          SmallVector<int, 8> Args;
          SmallVector<bool, 8> IsIndirectParam;
          getCowValueArgsOfApply(AI, CowValue, Args, IsIndirectParam);
          if (Args.empty())
            continue;
          for (auto Arg : Args) {
            if (Arg < 0)
              continue;
            auto isIndirect = IsIndirectParam[Arg];
            if (EA->canParameterEscape(AI, Arg, isIndirect)) {
              // The region is not active anymore after this point.
              CurrentlyActive[Id] = false;
              break;
            }
          }
        }
        continue;
      }

      if (isa<IsUniqueInst>(I)) {
        SILValue Op =
            stripUniquenessPreservingCastsAndProjections(I->getOperand(0));
        auto Root = RCIFI->getRCIdentityRoot(Op);
        DEBUG(llvm::dbgs() << "Found is_unique: "; I->dump();
              llvm::dbgs() << "\n"
                           << "RCRoot = " << Root << "\n");

        for (auto &KV : CowValueId) {
          auto CowValue = KV.getFirst();
          auto Id = KV.getSecond();
          if (Root == CowValue) {
            SILBuilderWithScope B(I);
            auto boolTy = SILType::getBuiltinIntegerType(
                1, I->getModule().getASTContext());
            auto yes = B.createIntegerLiteral(I->getLoc(), boolTy, 1);
            DEBUG(llvm::dbgs() << "Replace " << I << " by " << yes << "\n");
            I->replaceAllUsesWith(yes);
            I->eraseFromParent();
            continue;
          }
        }
      }

      if (auto *DSI = dyn_cast<DeallocStackInst>(I)) {
        auto Val = DSI->getOperand();

        for (auto &KV : CowValueId) {
          auto CowValue = KV.getFirst();
          auto Id = KV.getSecond();
          if (Val == CowValue) {
            // This is a kill.
            // The region is not active anymore after this point.
            CurrentlyActive[Id] = false;
            break;
          }
        }
        continue;
      }

      // Nothing else can change or escape the array buffer reference.
      continue;
    }
  }
  return Changes;
}

/// Find parameters that are knonw to be unique/non-atomic.
void NonAtomicRCTransformer::findUniqueParameters() {
  if (!F->getName().endswith("_NonAtomic"))
    return;
  // Self parameter is known to be non-atomic at this point.
  SILValue CowValue = F->getSelfArgument();
  if (!checkUniqueCowContainer(F, CowValue)) {
    assert(false && "Self parameter of a non-atomic function should be unique");
    return;
  }

  DEBUG(llvm::dbgs() << "\nThe following object is made thread-local as a Self "
                        "parameter of the non-atomic function "
                     << F->getName() << ":\n"
                     << CowValue << "\n");

  // TODO: Some parameters, like Self, are passed as inout.
  // We need to process them correctly, i.e. any storage pointer we get through
  // them is also unique.

  // Create a region for this cow value.
  // If we have seen a region for the same value already, we should
  // assign the same index to it.
  if (!CowValueId.count(CowValue)) {
    CowValueId[CowValue] = UniqueIdx++;
    IdToCowValue.push_back(CowValue);
  }
}

/// Compute a region where the buffer reference is non-escaping
/// and unique, i.e. it is thread-safe.
/// The region starts at a given apply instruction and ends
/// along each raeachable path as soon as there is an instruction
/// that may make the buffer non-unique (i.e. increase its RefCount)
/// or may write into the array and change the value of the buffer
/// reference. An apply site which can escape the buffer pointer
/// or may replace the buffer pointer is also such an example.

/// Find all make_mutable calls and optimize
/// the regions of code starting at those calls.
/// Inside those regions, any RC operations
/// on the array can be non-atomic. Subsequent
/// make_mutable calls on the same array can
/// be eliminated.
/// TODO: Support value-types other than Array, e.g.
/// Set or Dictionary.
void NonAtomicRCTransformer::findAllMakeUnique() {
  findUniqueParameters();
  // Find all make_mutable. This gives us the number
  // of differrent CowValues which are made unique
  // in the function.
  for (SILBasicBlock &BB : *F) {
    for (auto Iter = BB.begin(); Iter != BB.end();) {
      SILInstruction *I = &*Iter++;
      if (!isa<ApplyInst>(I)) {
        continue;
      }
      auto Call = isMakeUniqueCall(I);
      if (Call) {
        DEBUG(llvm::dbgs() << "Found a make_unique call:" << I << "\n");
      }
      if (Call && Call.getSelf() &&
          checkUniqueCowContainer(F, Call.getSelf())) {
        // Add to the set of makeUnique calls
        // The COW object that is made a thread-local by this call.
        auto CowValue = Call.getSelf();
        DEBUG(llvm::dbgs() << "\nThe following object is made thread-local: "
                           << CowValue << "\n";
              llvm::dbgs() << " by the instruction:\n"; I->dumpInContext());

        // Create a region for this cow value.
        // If we have seen a region for the same value already, we should
        // assign the same index to it.
        if (!CowValueId.count(CowValue)) {
          CowValueId[CowValue] = UniqueIdx++;
          IdToCowValue.push_back(CowValue);
        }
        continue;
      }
    }
  }
}

// Perform a basic scan over a function, look for RC instructions.
// If any of these instruction have a non-escaping operand, it
// is safe to make them non-atomic.
StateChanges NonAtomicRCTransformer::processNonEscapingRefCountingInsts() {
  StateChanges Changes = SILAnalysis::InvalidationKind::Nothing;
  // Search the whole function for stack promotable allocations.
  for (SILBasicBlock &BB : *F) {
    for (auto Iter = BB.begin(); Iter != BB.end();) {
      // The allocation instruction may be moved, so increment Iter prior to
      // doing the optimization.
      SILInstruction *I = &*Iter++;
      if (isEligableRefCountingInst(I)) {
        Changes = StateChanges(Changes | tryNonAtomicRC(I));
      }
    }
  }
  return Changes;
}

StateChanges NonAtomicRCTransformer::processUniqenessRegions() {
  // Identify the beginning of all uniqueness regions.
  findAllMakeUnique();
  if (CowValueId.empty())
    return SILAnalysis::InvalidationKind::Nothing;
  DF.initStates(CowValueId.size());
  // Find the places where regions end.
  scanAllBlocks();
  // Perform a datafow analysis to find out the span
  // of each region.
  DF.compute();
  // Now walk the regions and perform the transformations.
  return transformAllBlocks();
}

StateChanges NonAtomicRCTransformer::process() {
  DEBUG(llvm::dbgs() << "\nAbout to process function:\n"; F->dump());
  auto ChangesUniquness = processUniqenessRegions();
  auto ChangesRefCounting = processNonEscapingRefCountingInsts();

  if (ChangesUniquness || ChangesRefCounting) {
    DEBUG(llvm::dbgs() << "\n\nFunction after the transformation:"; F->dump());
  }

  return StateChanges(ChangesUniquness | ChangesRefCounting);
}

//===----------------------------------------------------------------------===//
//                              Top Level Driver
//===----------------------------------------------------------------------===//

class NonAtomicRC : public SILFunctionTransform {
public:
  NonAtomicRC() {}

private:
  /// The entry point to the transformation.
  void run() override {
    if (!PerformNonAtomicOpts)
      return;

    DEBUG(llvm::dbgs() << "** NonAtomicRC for " << getFunction()->getName()
                       << " **\n");

    auto *EA = PM->getAnalysis<EscapeAnalysis>();
    auto *RCIA = PM->getAnalysis<RCIdentityAnalysis>();

    SILFunction *F = getFunction();
    auto *ConGraph = EA->getConnectionGraph(F);
    if (ConGraph) {
      NonAtomicRCTransformer Transformer(PM, F, ConGraph, EA, RCIA->get(F));
      auto Changes = Transformer.process();
      if (Changes) {
        PM->invalidateAnalysis(F, Changes);
      }
    }
  }

  StringRef getName() override { return "NonAtomicRC"; }
};

} // end anonymous namespace

SILTransform *swift::createNonAtomicRC() { return new NonAtomicRC(); }
