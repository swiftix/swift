//===-------  RegionBasedNonAtomicRC.cpp - Use non-atomic reference counting  -------===//
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
#include "swift/SILOptimizer/Analysis/CallerAnalysis.h"
#include "swift/SILOptimizer/Analysis/DominanceAnalysis.h"
#include "swift/SILOptimizer/Analysis/EscapeAnalysis.h"
#include "swift/SILOptimizer/Analysis/RCIdentityAnalysis.h"
#include "swift/SILOptimizer/Analysis/ValueTracking.h"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "swift/SILOptimizer/Utils/Generics.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"

STATISTIC(NumRegionBasedNonAtomicRC,
          "Number of region-based non-atomic RC operations");

llvm::cl::opt<bool> PerformRegionBasedNonAtomicOpts(
    "region-based-non-atomic-opts", llvm::cl::init(true),
    llvm::cl::desc(
        "Enable region-based non-atomic reference counting optimizations"));

using namespace swift;

namespace {
// Bitvector implementation to be used for the dataflow analysis.
typedef llvm::SmallBitVector StateBitVector;

#ifndef NDEBUG
static llvm::raw_ostream &operator<<(llvm::raw_ostream &stream, llvm::BitVector &BV) {
  unsigned size = BV.size();
  stream << "[ ";
  for (unsigned i = 0; i < size; ++i)
    stream << BV[i] << " ";
  stream << ']';
  return stream;
}

static llvm::raw_ostream &operator<<(llvm::raw_ostream &stream,
                              llvm::SmallBitVector &BV) {
  unsigned size = BV.size();
  stream << "[ ";
  for (unsigned i = 0; i < size; ++i)
    stream << BV[i] << " ";
  stream << ']';
  return stream;
}
#endif

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
  const SILFunction *F;

  // Maps a basic block to its numeric id
  llvm::DenseMap<const SILBasicBlock *, int> BlockIds;

  // Dataflow analysis state for each BB.
  // Indexed by the ids assigned in BlockIds.
  std::vector<BlockState> BlockStates;

  // Bit verctor length used by the dataflow analysis.
  // It represents the number of different properties
  // being tracked.
  unsigned StateLength;

public:
  Dataflow(const SILFunction *F);
  int getBlockIdx(const SILBasicBlock *BB) const { return BlockIds.lookup(BB); }
  unsigned getStateLength() const { return StateLength; }
  void setStateLength(unsigned Length) {
    assert(!StateLength);
    StateLength = Length;
  }
  virtual void initStates();
  virtual StateBitVector mergePredecessorStates(const SILBasicBlock *BB);
  virtual void compute();
  BlockState &getBlockState(const SILBasicBlock *BB) {
    return BlockStates[BlockIds[BB]];
  }
  virtual void dump();
  virtual ~Dataflow() {}
};

Dataflow::Dataflow(const SILFunction *F) : F(F), StateLength(0) {
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
/// (^ OUT(Pred)) for all Pred from predecessors of BB
StateBitVector Dataflow::mergePredecessorStates(const SILBasicBlock *BB) {
  if (BB->pred_empty())
    return getBlockState(BB).In;
  StateBitVector Result(getStateLength(), true);
  for (auto Pred : BB->getPreds()) {
    // Don't take into account its own Out set.
    //if (Pred == BB)
    //  continue;
    Result &= getBlockState(Pred).Out;
  }
  return Result;
}

/// Main loop of the dataflow analysis.
/// TODO: Make it iterate only once for functions that do not have loops.
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
  UniquenessDataflow(const SILFunction *F) : Dataflow(F) {}

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

class RegionBasedNonAtomicRCTransformer {
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

  // Set of arguments of the current functon known to be unique.
  // Typically, such arguments are the arguments of functions
  // generated automatically based on generate.nonatomic
  // attribute.
  llvm::SmallVector<SILValue, 4> UniqueArgs;

  // The set of basic blocks containing instructions
  // that are interesting for this optimization.
  llvm::SmallPtrSet<SILBasicBlock *, 32> CandidateBBs;
  unsigned UniqueIdx;

  enum CandidateKind {
    CANDIDATE_UNKNOWN,
    CANDIDATE_STORE_DEST,
    CANDIDATE_STORE_SRC,
    CANDIDATE_GEN,
    CANDIDATE_KILL,
    CANDIDATE_UNIQUE,
    CANDIDATE_RC,
    CANDIDATE_IS_NATIVE_TYPE_CHECKED
  };

  struct Candidate {
    SILInstruction *I;
    SILValue CowValue;
    CandidateKind Kind;
    Candidate(SILInstruction *I, SILValue CowValue, CandidateKind Kind)
        : I(I), CowValue(CowValue), Kind(Kind) {}
  };

  // The set of instructions that are interesting for this
  // optimization.
  llvm::SmallVector<Candidate, 32> Candidates;


public:
  RegionBasedNonAtomicRCTransformer(SILPassManager *PM, SILFunction *F,
                                    EscapeAnalysis::ConnectionGraph *ConGraph,
                                    EscapeAnalysis *EA,
                                    RCIdentityFunctionInfo *RCIFI)
      : PM(PM), F(F), ConGraph(ConGraph), EA(EA), RCIFI(RCIFI), DF(F),
        UniqueIdx(0) {}

  StateChanges process();

private:
  StateChanges processUniqenessRegions();
  bool isCowValue(ValueBase *CowStruct, SILValue Value);
  bool isRCofCowValueAt(ValueBase *CowStruct, SILInstruction *Inst);
  bool isStoreAliasingCowValue(ValueBase *CowStruct, SILValue Dest);
  void findAllMakeUnique();
  void findUniqueParameters();
  void scanAllBlocks();
  void scanBasicBlock(SILBasicBlock *BB);
  StateChanges transformAllBlocks();
  bool getCowValueArgsOfApply(FullApplySite AI, SILValue CowValue,
                              SmallVectorImpl<int> &Args,
                              SmallVectorImpl<bool> &IsIndirectParam);
  void markAsCandidate(SILInstruction *I, SILValue CowValue, CandidateKind Kind);
  void replaceByNonAtomicApply(FullApplySite AI);
  SILFunction *createNonAtomicFunction(SILFunction *F);
  bool isBeneficialToClone(SILFunction *F);
  bool isUniqueArg(SILValue Arg);
};

namespace {
/// \brief A very simple SILCloner subclass which clones an existing function
/// without any changes.
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
  auto *Fn = M.createFunction(
      SILLinkage::Shared, ClonedName, ClonedTy, Orig->getGenericEnvironment(),
      Orig->getLocation(), Orig->isBare(), IsNotTransparent, Orig->isFragile(),
      Orig->isThunk(), Orig->getClassVisibility(), Orig->getInlineStrategy(),
      Orig->getEffectsKind(), Orig, Orig->getDebugScope());
  for (auto &Attr : Orig->getSemanticsAttrs()) {
    Fn->addSemanticsAttr(Attr);
  }
  Fn->setDeclCtx(Orig->getDeclContext());
  return Fn;
}

/// \brief Populate the body of the cloned function.
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

/// Produce an exact clone of the function, but under a new name.
static SILFunction *getClonedFunction(SILFunction *OrigF, StringRef NewName) {
  FunctionCloner Cloner(OrigF, NewName);
  Cloner.populateCloned();
  return Cloner.getCloned();
}

typedef SILAnalysis::InvalidationKind StateChanges;

/// Try to strip all casts and projections as long they preserve the
/// uniqueness of the value.
static SILValue stripUniquenessPreservingCastsAndProjections(SILValue V) {
  while (V) {
    V = stripAddressProjections(V);
    auto V2 = stripCasts(V);
    if (auto *UAC = dyn_cast<UncheckedAddrCastInst>(V2)) {
      if (UAC->getType() ==
          SILType::getNativeObjectType(UAC->getModule().getASTContext())
              .getAddressType()) {
        V = UAC->getOperand();
        continue;
      }
    }
    if (V2 == V)
      return V;
    V = V2;
  }
  return V;
}
// Create a version of the function which would use non-atomic
// reference counting for a given set of arguments.
SILFunction *
RegionBasedNonAtomicRCTransformer::createNonAtomicFunction(SILFunction *F) {
  // TODO: Check if non-atomic version exists already and return
  // it if available.
  if (F->getName().endswith("_NonAtomic"))
    return F;
  // Otherwise clone and rewrite ref-counting operations in the body.
  SILModule &Mod = F->getModule();

  // Produce a mangled name of a non-atomic function.
  // TODO: Extend mangler to support non-atomic/unique arguments encodings.
  // This would allow for providing the non-atomic/unique attribute per parameter.
  // More over, it would make it easy to access this information later.
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
  PM->addFunctionToWorklist(NewF, F);
  DEBUG(llvm::dbgs() << "Created a new non-atomic function: " << NewF->getName()
                     << "\n";
        NewF->dump());
  return NewF;
}

/// Check if it is beneficial to clone F if its
/// Self argument can be used non-atomically.
bool RegionBasedNonAtomicRCTransformer::isBeneficialToClone(SILFunction *F) {
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
void RegionBasedNonAtomicRCTransformer::replaceByNonAtomicApply(
    FullApplySite AI) {
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
  I->setNonAtomic();
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

/// Obtain the underlying object by stripoping casts as well
/// index and address projections.
static SILValue obtainUnderlyingObject(SILValue V) {
  while (true) {
    SILValue V2 =
        stripIndexingInsts(stripUniquenessPreservingCastsAndProjections(V));
    if (V2 == V)
      return V2;
    V = V2;
  }
}

static ArraySemanticsCall isMakeUniqueCall(ArraySemanticsCall &Call) {
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
  return ArraySemanticsCall(&*Call, "non-existing", false);
}

/// Is it an instruction that creates a uniquelly referenced
/// object?
static ArraySemanticsCall isMakeUniqueCall(SILInstruction *I) {
  // TODO: Handle other COW types here?
  // May be each mutating function call on a COW object should be
  // considered as make_unique?
  ArraySemanticsCall Call(I);
  return isMakeUniqueCall(Call);
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
bool checkUniqueCowContainer(SILFunction *F, SILValue CowContainer) {
  if (isa<AllocStackInst>(CowContainer))
    return true;

  SILArgument *Arg = dyn_cast<SILArgument>(CowContainer);
  if (!Arg || !F) {
    DEBUG(
        llvm::dbgs()
            << "    Skipping COW object: Not an argument or local variable!\n";
        CowContainer->dump());
    return false;
  }

  // Check that the argument is passed as an inout type. This means there are
  // no aliases accessible within this function scope.
  auto Params = F->getLoweredFunctionType()->getParameters();
  ArrayRef<SILArgument *> FunctionArgs = F->begin()->getBBArgs();
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

/// Check if Arg is a known unique function argument.
bool RegionBasedNonAtomicRCTransformer::isUniqueArg(SILValue Arg) {
  return std::find(UniqueArgs.begin(), UniqueArgs.end(), Arg) !=
         UniqueArgs.end();
}

bool RegionBasedNonAtomicRCTransformer::isCowValue(ValueBase *CowStruct,
                                                   SILValue Value) {
  auto Root = RCIFI->getRCIdentityRoot(Value);
  if (Root == CowStruct)
    return true;
  auto *CowLoad = dyn_cast<LoadInst>(Root);
  if (!CowLoad)
    return false;

  SILValue LoadOperand = CowLoad->getOperand();
  if (LoadOperand == CowStruct)
    return true;

  // Is it an RC operation on the buffer reference?
 //          stripAddressProjections(CowLoad->getOperand())) == CowStruct)
  if (!CowStruct->getType().isAddress() &&
      RCIFI->getRCIdentityRoot(stripUniquenessPreservingCastsAndProjections(
          LoadOperand)) == CowStruct)

    return true;

  // If CowStruct is an inout parameter, see if this is the following pattern:
  // %load1 = load (projection CowStruct)
  // %enum_data = unchecked_enum_data %load1,
  // %load2 = load (projection %enum_data)
  //
  // FIXME: This pattern happens a lot with the current implementation of COW
  // data ctypes in the Swift standard library, because all of them are structs,
  // containing a pointer to the buffer. If the internal representation of
  // the COW data types does not follow this pattern, the code below needs
  // to be adjusted.
  // One possible way to get a more general solution would be to mark
  // certain properties of the COW data type with a special attribute,
  // which could indicate that they are buffer (i.e. COW sub-parts) pointers.
  if (!CowStruct->getType().isAddress()) {
    assert(isUniqueArg(CowStruct) &&
           "Only COW objects passed as inout may have address types");
    return false;
  }

  auto Op = stripUniquenessPreservingCastsAndProjections(LoadOperand);
  auto *UEDI = dyn_cast<UncheckedEnumDataInst>(Op);
  if (!UEDI)
    return false;
  SILValue UncheckedEnumDataOp =
      stripUniquenessPreservingCastsAndProjections(UEDI->getOperand());
  auto *LI = dyn_cast<LoadInst>(UncheckedEnumDataOp);
  if (!LI)
    return false;
  auto CowLoadOperand =
      stripUniquenessPreservingCastsAndProjections(LI->getOperand());
  if (RCIFI->getRCIdentityRoot(CowLoadOperand) == CowStruct)
    return true;

  return false;
}

/// Check that the array value stored in \p CowStruct is operand of this RC by
/// \Inst.
/// TODO: Support other COW types, not only array.
bool RegionBasedNonAtomicRCTransformer::isRCofCowValueAt(ValueBase *CowStruct,
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
bool RegionBasedNonAtomicRCTransformer::isStoreAliasingCowValue(
    ValueBase *CowStruct, SILValue Dest) {
  auto Root = RCIFI->getRCIdentityRoot(Dest);

  // Is it overwriting the array struct?
  if (Root == CowStruct)
    return true;

  // If this is a store of a trivial field (i.e. containing no references),
  // then it cannot alias any buffer pointers.
  if (Dest->getType().getObjectType().isTrivial(F->getModule()))
    return true;

  // Is it a store to a field of a COW struct, e.g. to the buffer reference?
  // For the moment, consider stores into any fields of a COW data structure
  // as aliasing. This is very pessimistic, but correct.
  // TODO: Make this check more precise? We want to detect stores into
  // fileds containing a reference to the COW-buffers. Such fields are likely
  // to be marked in a special way in the future.
  //if (RCIFI->getRCIdentityRoot(stripAddressProjections(Root)) == CowStruct)
  if (RCIFI->getRCIdentityRoot(stripUniquenessPreservingCastsAndProjections(Root)) == CowStruct)
    return true;

  return false;
}

/// Scan all basic blocks and intialize GEN, KILL and OUT sets.
void RegionBasedNonAtomicRCTransformer::scanAllBlocks() {
  // Unique/non-atomic function parameters are in
  // the IN set of the entry block.
  for (auto Arg : F->getArguments()) {
    if (isUniqueArg(Arg)) {
      auto Id = CowValueId[Arg];
      DF.getBlockState(&*F->begin()).In[Id] = true;
      DEBUG(llvm::dbgs() << "Adding a unique parameter into IN set of the "
                            "entry basic block: ";
            Arg->dump());
    }
  }

  for (auto &BB : *F) {
    scanBasicBlock(&BB);
  }
}

// Get a set of apply arguments that may alias a given COW value.
// Returns true, if there is at least one aliasing argument.
bool RegionBasedNonAtomicRCTransformer::getCowValueArgsOfApply(
    FullApplySite AI, SILValue CowValue, SmallVectorImpl<int> &Args,
    SmallVectorImpl<bool> &IsIndirectParam) {
  if (!AI.getInstruction())
    return true;
  DEBUG(llvm::dbgs() << "Analyzing if the following apply instruction is a candidate:\n";
        AI.getInstruction()->dumpInContext());
  bool Result = false;
  for (unsigned i = 0, e = AI.getArguments().size(); i < e; ++i) {
    auto Arg = AI.getArgument(i);
    bool isAlias = isCowValue(CowValue, Arg);
    DEBUG(llvm::dbgs() << "Analyzing if the the argument aliases a COW value:\nArgument:\n";
          CowValue->dumpInContext();
          llvm::dbgs() << "COW value:\n";
          Arg->dumpInContext();
          llvm::dbgs() << "Is alias?: " << isAlias << "\n");
    if (isAlias) {
      Args.push_back(i);
      Result = true;
    } else
      Args.push_back(-1); // -1 means that argument is not aliasing CowValue.
  }
  if (Args.empty())
    return false;
  auto FnTy = AI.getSubstCalleeType();

  for (auto ResultInfo : FnTy->getIndirectResults()) {
    IsIndirectParam.push_back(ResultInfo.isIndirect());
  }

  for (auto ParamInfo : FnTy->getParameters()) {
    IsIndirectParam.push_back(ParamInfo.isIndirect());
  }
  assert(Args.size() == IsIndirectParam.size());
  DEBUG(llvm::dbgs() << "The apply instruction is a candidate\n");
  return Result;
}

void RegionBasedNonAtomicRCTransformer::markAsCandidate(SILInstruction *I,
                                                        SILValue CowValue,
                                                        CandidateKind Kind) {
  Candidates.push_back(Candidate(I, CowValue, Kind));
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
// Initialize the GEN, KILL and OUT sets of the basic block.
// - GEN consists of those definitions CowValues that are
// made unique, but not killed afterwards in the BB.
// - KILL consists of CowValues that are killed in the BB
// - The initial value of OUT is basically equivalent to GEN set.
//
// During the scan, remember the "interesting" instructions so
// that anything else can be skipped during the transformation stage.
//
// TODO: Candidates should be a vector of pairs.
// Each pair should be (instruction, CowValue it affects).
// This would allow for avoiding iteration over all instructions
// in the transformAllBlocks. More over, it would also allow
// for avoiding doing the same checks in transformAllBlocks.
void RegionBasedNonAtomicRCTransformer::scanBasicBlock(SILBasicBlock *BB) {
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
          markAsCandidate(I, CowValue, CANDIDATE_STORE_DEST);
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
          markAsCandidate(I, CowValue, CANDIDATE_STORE_SRC);
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
        markAsCandidate(I, CowValue, CANDIDATE_GEN);

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
          markAsCandidate(I, SILValue(), CANDIDATE_IS_NATIVE_TYPE_CHECKED);
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
          DEBUG(llvm::dbgs() << "Checked args size:" << Args.size() << "\n");
          if (Args.size()) {
            DEBUG(llvm::dbgs() << "Kill operation for CowValue:\n"
                               << CowValue;
                  I->dumpInContext());
            LastSeenOp[Id] = Kill;
            markAsCandidate(I, CowValue, CANDIDATE_KILL);
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

        auto hasAliases =
            getCowValueArgsOfApply(AI, CowValue, Args, IsIndirectParam);
        if (Args.empty() || !hasAliases)
          continue;
        for (auto Arg : Args) {
          if (Arg < 0)
            continue;
          // If an argument aliases a CowValue, mark the call instruction
          // as a candiate.
          auto isIndirect = IsIndirectParam[Arg];
          if (EA->canParameterEscape(AI, Arg, isIndirect)) {
            LastSeenOp[Id] = Kill;
            KilledCowValues[Id] = true;
            markAsCandidate(I, CowValue, CANDIDATE_KILL);
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
          markAsCandidate(I, CowValue, CANDIDATE_KILL);
          DEBUG(llvm::dbgs() << "Kill operation for CowValue\n"
                             << CowValue;
                I->dumpInContext());
          break;
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
        if (Root == CowValue) {
          markAsCandidate(I, CowValue, CANDIDATE_UNIQUE);
          break;
        }
      }
      continue;
    }

    if (auto *RC = dyn_cast<RefCountingInst>(I)) {
      auto Ref = RC->getOperand(0);
      for (auto &KV : CowValueId) {
        auto CowValue = KV.getFirst();
        // Check if it kills any non-local region.
        if (isRCofCowValueAt(CowValue, I)) {
          markAsCandidate(I, CowValue, CANDIDATE_RC);
          break;
        }
      }
      continue;
    }
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
    // Remember only those GEN instructions that are not followed
    // by a KILL, which means that they will be in the OUT set of this BB.
    if (LastSeenOp[i] == Gen)
      DF.getBlockState(BB).Gen[i] = true;
  }

  // Initialize OUT sets with GEN sets.
  DF.getBlockState(BB).Out = DF.getBlockState(BB).Gen;


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
StateChanges RegionBasedNonAtomicRCTransformer::transformAllBlocks() {
  DEBUG(llvm::dbgs() << "** Transform basic blocks inside " << F->getName()
                     << " **\n");

  // TODO: Iterate over candidate instructions only. No need
  // to iterate over all instructions in the function.
  StateChanges Changes = SILAnalysis::InvalidationKind::Nothing;
  SILBasicBlock *LastBB = nullptr;
  BlockState *BBState = nullptr;

  // The set of currently active uniqness regions.
  // Indexed by the id of a CowValue being tracked.
  // Initialized with the IN set of the current basic block.
  StateBitVector CurrentlyActive;

  for (auto &C : Candidates) {
    auto I = C.I;
    auto CowValue = C.CowValue;
    auto *BB = I->getParent();
    auto Kind = C.Kind;
    if (BB != LastBB) {
      BBState = &DF.getBlockState(BB);
      CurrentlyActive = BBState->In;
    }
    LastBB = BB;

    DEBUG(llvm::dbgs() << "** Transform a candidate instruction:\n";
          I->dumpInContext());

    if (auto *RC = dyn_cast<RefCountingInst>(I)) {
      assert(Kind == CandidateKind::CANDIDATE_RC);
      // If the region for a given CowValue is active and
      // if this is the array buffer reference or if this is
      // the array container itself, then it can be replaced
      // by a non-atomic variant.
      auto Id = CowValueId[CowValue];
      if (CurrentlyActive.test(Id)) {
        Changes =
            StateChanges(Changes | SILAnalysis::InvalidationKind::Instructions);
        markAsNonAtomic(RC);
        DEBUG(llvm::dbgs() << "RC operation inside make_mutable region can be "
                              "non-atomic: ";
              RC->dump());
      }
      continue;
    }

    // Check if instruction may overwrite the array buffer reference in the
    // container.
    if (auto *SI = dyn_cast<StoreInst>(I)) {
      auto CowValue = C.CowValue;

      assert(Kind == CandidateKind::CANDIDATE_STORE_DEST ||
             Kind == CandidateKind::CANDIDATE_STORE_SRC);
      assert(CowValue);

      auto Id = CowValueId[CowValue];

      if (Kind == CandidateKind::CANDIDATE_STORE_DEST) {
        DEBUG(llvm::dbgs() << "Kill operation for CowValue\n"
                           << CowValue;
              I->dumpInContext());
        // The region is not active anymore after this point.
        CurrentlyActive[Id] = false;
        continue;
      }

      // This is a store of a CowValue into a different location,
      // which may create an alias.

      // This is a kill.
      CurrentlyActive[Id] = false;
      DEBUG(llvm::dbgs() << "Kill operation for CowValue\n"
                         << CowValue;
            I->dumpInContext());
      continue;
    }

    if (auto AI = FullApplySite::isa(I)) {
      ArraySemanticsCall ArrayCall(AI.getInstruction());
      if (ArrayCall &&
          (ArrayCall.getKind() == ArrayCallKind::kGuaranteeMutable ||
           ArrayCall.getKind() == ArrayCallKind::kMutateUnknown)) {
        assert(Kind == CandidateKind::CANDIDATE_GEN);

        // TODO: Call a non-atomic version of the function?
        // The COW object that is made a thread-local by this call.
        auto Id = CowValueId[CowValue];
        auto *Callee = AI.getCalleeFunction();

        if (CurrentlyActive.test(Id) &&
            Callee->hasSemanticsAttr("generate.nonatomic")) {
          DEBUG(llvm::dbgs() << "Non-atomic version of the call can be used:\n";
                AI.getInstruction()->dumpInContext());
          replaceByNonAtomicApply(AI);
        }
        // Start of a uniqeness region.
        CurrentlyActive[Id] = true;
        continue;
      }

      if (ArrayCall && ArrayCall.getKind() == ArrayCallKind::kMakeMutable) {
        assert(Kind == CandidateKind::CANDIDATE_GEN);

        // Add to the set of makeUnique calls
        // The COW object that is made a thread-local by this call.
        auto CowValue = ArrayCall.getSelf();

        // Check if this make_mutable is inside an existing region for the
        // same CowValue. If this is the case, then it can be removed.
        // The region may have started either in this BB or outside.
        // TODO: It can be that make_mutable is not only making something
        // mutable but does more. In this case it cannot be removed.
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
        assert(Kind == CandidateKind::CANDIDATE_IS_NATIVE_TYPE_CHECKED);
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
          continue;
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
          DEBUG(llvm::dbgs() << "Non-atomic version of the call can be used:\n";
                AI.getInstruction()->dumpInContext());
          replaceByNonAtomicApply(AI);
          Changes =
              StateChanges(Changes | SILAnalysis::InvalidationKind::Calls);
          // TODO: Rescan the release instruction?
          continue;
        }
      }

      if (ArrayCall) {
        assert(Kind == CandidateKind::CANDIDATE_KILL);
        // Check whose uniqueness is changed.
        auto Id = CowValueId[CowValue];
        CurrentlyActive[Id] = false;
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
      // equivalent to a store to the array and thus ends the region.
      // If it escapes inside the function, it also ends the region.
      // But what if it is only read inside the function? it would be nice if
      // EA would say it does not escape.

      // End of a uniqeness region.
      assert(Kind == CandidateKind::CANDIDATE_KILL);
      auto Id = CowValueId[CowValue];
      CurrentlyActive[Id] = false;
      continue;
    }

    if (isa<IsUniqueInst>(I)) {
     assert(Kind == CandidateKind::CANDIDATE_UNIQUE);
     SILValue Op =
          stripUniquenessPreservingCastsAndProjections(I->getOperand(0));
      auto Root = RCIFI->getRCIdentityRoot(Op);
      DEBUG(llvm::dbgs() << "Found is_unique: "; I->dump();
            llvm::dbgs() << "\n"
                         << "RCRoot = " << Root << "\n");

      // The result of this check will be always true, because
      // it is inside a uniqueness region.
      auto Id = CowValueId[CowValue];
      SILBuilderWithScope B(I);
      auto boolTy =
          SILType::getBuiltinIntegerType(1, I->getModule().getASTContext());
      auto yes = B.createIntegerLiteral(I->getLoc(), boolTy, 1);
      DEBUG(llvm::dbgs() << "Replace " << I << " by " << yes << "\n");
      I->replaceAllUsesWith(yes);
      I->eraseFromParent();
      Changes =
          StateChanges(Changes | SILAnalysis::InvalidationKind::Instructions);
      continue;
    }

    if (auto *DSI = dyn_cast<DeallocStackInst>(I)) {
      // End of a uniqueness region.
      assert(Kind == CandidateKind::CANDIDATE_KILL);
      auto Id = CowValueId[CowValue];
      CurrentlyActive[Id] = false;
      continue;
    }

    // Nothing else can change or escape the array buffer reference.
    llvm::dbgs() << "Unexpected candidate was found:\n";
    I->dumpInContext();
    llvm::dbgs() << "\n";
    llvm_unreachable("Unexpected candidate was found");
  }
  return Changes;
}

/// Find parameters that are knonw to be unique/non-atomic.
void RegionBasedNonAtomicRCTransformer::findUniqueParameters() {
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
  // them is also unique. And this part seems to be rather non-trivial. It may
  // even be that is is dependent on the internal representation of a COW-type,
  // i.e. the processing is different for different types.

  // Create a region for this cow value.
  // If we have seen a region for the same value already, we should
  // assign the same index to it.
  if (!CowValueId.count(CowValue)) {
    CowValueId[CowValue] = UniqueIdx++;
    IdToCowValue.push_back(CowValue);
    UniqueArgs.push_back(CowValue);
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
void RegionBasedNonAtomicRCTransformer::findAllMakeUnique() {
  findUniqueParameters();
  // Find all make_mutable. This gives us the number
  // of differrent CowValues which are made unique
  // in the current function.
  for (SILBasicBlock &BB : *F) {
    for (auto Iter = BB.begin(); Iter != BB.end();) {
      SILInstruction *I = &*Iter++;

      // TODO: Check for non-escaping Cow Containers like
      // local variables and by-value arguments? Or let it
      // be handled by the non-region-based non-atomic-rc pass?

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

StateChanges RegionBasedNonAtomicRCTransformer::processUniqenessRegions() {
  // Identify the beginning of all uniqueness regions.
  findAllMakeUnique();
  // Bail if there are now COW values to be tracked.
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

StateChanges RegionBasedNonAtomicRCTransformer::process() {
  DEBUG(llvm::dbgs() << "\nAbout to process function:\n"; F->dump());
  auto ChangesUniquness = processUniqenessRegions();

  if (ChangesUniquness) {
    DEBUG(llvm::dbgs() << "\n\nFunction after the transformation:"; F->dump());
  }

  return StateChanges(ChangesUniquness);
}

//===----------------------------------------------------------------------===//
//                              Top Level Driver
//===----------------------------------------------------------------------===//

class RegionBasedNonAtomicRC : public SILFunctionTransform {
public:
  RegionBasedNonAtomicRC() {}

private:
  /// The entry point to the transformation.
  void run() override {
    if (!PerformRegionBasedNonAtomicOpts)
      return;

    DEBUG(llvm::dbgs() << "** Start RegionBasedNonAtomicRC for "
                       << getFunction()->getName() << " **\n");

    auto *EA = PM->getAnalysis<EscapeAnalysis>();
    auto *RCIA = PM->getAnalysis<RCIdentityAnalysis>();

    SILFunction *F = getFunction();
    auto *ConGraph = EA->getConnectionGraph(F);
    if (ConGraph) {
      DEBUG(ConGraph->dump());
      RegionBasedNonAtomicRCTransformer Transformer(PM, F, ConGraph, EA,
                                                    RCIA->get(F));
      auto Changes = Transformer.process();
      if (Changes) {
        PM->invalidateAnalysis(F, Changes);
      }
    }
    DEBUG(llvm::dbgs() << "** End RegionBasedNonAtomicRC for "
                       << getFunction()->getName() << " **\n");
  }

  StringRef getName() override { return "RegionBasedNonAtomicRC"; }
};

} // end anonymous namespace

SILTransform *swift::createRegionBasedNonAtomicRC() { return new RegionBasedNonAtomicRC(); }
