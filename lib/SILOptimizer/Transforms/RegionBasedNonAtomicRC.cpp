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

/// This pass implements a region-based transformation that may convert atomic
/// reference-counting operations into non-atomic ones and can eliminate
/// obsolette is_unique checks, whose outcomes are statically known.
///
/// The pass proceeds in the following phases:
/// - First, it scans a function, finds all interesting RC roots and any
/// instructions that may make those roots unique or can destroy the
/// uniqueness of the RC roots.
/// Instructions making RC roots unique are considered to begin a region.
/// Instructions destroying the uniquness property are considered to end a
/// region. All regions are constructed on a per RC root basis.
///
/// - Based on the collected information, a forward data flow analysis is
/// performed. The output of this analysis is a set of regions per RC root.
///
/// - The final phase visits all instructions inside regions. All RC
/// instructions inside a region can be made non-atomic. All uniqueness checks
/// inside a region are known to be true and therefore are replaced by a true
/// value.
///
/// Future extentions: The current implementation tracks the uniquness
/// property. But for replacing atomic RC operations by non-atomic ones it is
/// enough to track the thread-locality property, which is less strict.
/// For example, it is sometimes possible to prove that a given RC root is
/// thread-local even if the referred object is not uniquely referenced.

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
  enum RegionMode {
    UNIQUENESS_REGIONS,
    THREAD_LOCAL_REGIONS,
  };
  SILPassManager *PM;
  SILFunction *F;
  EscapeAnalysis::ConnectionGraph *ConGraph;
  EscapeAnalysis *EA;
  RCIdentityFunctionInfo *RCIFI;

  // TODO: Track separetly uniquness and threa-localality
  // using dataflow analysis?
  UniquenessDataflow UniquenessDF;
  UniquenessDataflow ThreadLocalDF;

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

  RegionMode Mode;

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
    RegionMode Mode;
    Candidate(SILInstruction *I, SILValue CowValue, CandidateKind Kind,
              RegionMode Mode)
        : I(I), CowValue(CowValue), Kind(Kind), Mode(Mode) {}
  };

  // The set of instructions that are interesting for this
  // optimization.
  // Candidate instructions inside a basic block are stored
  // in the order of their execution.
  llvm::SmallVector<Candidate, 32> Candidates;
  // Set of instructions removed by the pass.
  SmallPtrSet<SILInstruction *, 32> RemovedInstructions;

  enum DataflowOp { None, Gen, Kill };

  // Helper type to track the state of the current basic block scan.
  struct ScanState {
    llvm::SmallVector<DataflowOp, 32> LastSeenOp;
    // Remember which CowValue regions were killed in this BB.
    StateBitVector KilledCowValues;
    StateBitVector EscapedCowValues;
    UniquenessDataflow &DF;
    ScanState(UniquenessDataflow &DF) : DF(DF) {
      LastSeenOp.resize(DF.getStateLength());
      KilledCowValues.resize(DF.getStateLength());
      EscapedCowValues.resize(DF.getStateLength());
    }
  };

  // Helper type to track the state of the current basic block
  // during the transformation.
  struct TransformState {
    StateChanges Changes;
    RegionMode Mode;
    SILValue CowValue;
    CandidateKind Kind;
    // The set of currently active uniqness regions.
    // Indexed by the id of a CowValue being tracked.
    // Initialized with the IN set of the current basic block.
    StateBitVector CurrentlyActive;
    StateBitVector EscapedCowValues;
    SILInstruction *I;
    Candidate *C;
  };

public:
  RegionBasedNonAtomicRCTransformer(SILPassManager *PM, SILFunction *F,
                                    EscapeAnalysis::ConnectionGraph *ConGraph,
                                    EscapeAnalysis *EA,
                                    RCIdentityFunctionInfo *RCIFI)
      : PM(PM), F(F), ConGraph(ConGraph), EA(EA), RCIFI(RCIFI),
        UniquenessDF(F), ThreadLocalDF(F),
        UniqueIdx(0), Mode(UNIQUENESS_REGIONS) {}

  StateChanges process();

private:
  StateChanges processUniqenessRegions();
  bool isCowValue(ValueBase *CowStruct, SILValue Value);
  bool isRCofCowValueAt(ValueBase *CowStruct, SILInstruction *Inst);
  bool isStoreAliasingCowValue(ValueBase *CowStruct, SILValue Dest);
  void findAllMakeUnique();
  void findUniqueParameters();
  void scanAllBlocks(UniquenessDataflow &DF);
  void scanBasicBlock(SILBasicBlock *BB, UniquenessDataflow &DF);
  StateChanges transformAllBlocks(RegionMode Mode);
  bool getCowValueArgsOfApply(FullApplySite AI, SILValue CowValue,
                              SmallVectorImpl<int> &Args,
                              SmallVectorImpl<bool> &IsIndirectParam);
  void markAsCandidate(SILInstruction *I, SILValue CowValue, CandidateKind Kind,
                       RegionMode Mode);
  void replaceByNonAtomicApply(FullApplySite AI);
  SILFunction *createNonAtomicFunction(SILFunction *F);
  bool isBeneficialToClone(SILFunction *F);
  bool isUniqueArg(SILValue Arg);
  void computeUniqenesssRegions();
  void computeThreadLocalRegions();
  bool checkUniqueCowContainer(SILFunction *F, SILValue CowContainer);

  void scanStoreInst(StoreInst *SI, ScanState &S);
  void scanDeallocStackInst(DeallocStackInst *DSI, ScanState &S);
  void scanRefCountingInst(RefCountingInst *RC, ScanState &S);
  void scanIsUniqueInst(SILInstruction *I, ScanState &S);
  void scanApplyInst(FullApplySite AI, ScanState &S);

  void transformStoreInst(StoreInst *SI, TransformState &S);
  void transformApplyInst(FullApplySite AI, TransformState &S);
  void transformDeallocStackInst(DeallocStackInst *DSI, TransformState &S);
  void transformIsUniqueInst(SILInstruction *I, TransformState &S);
  void transformRefCountingInst(RefCountingInst *RC, TransformState &S);
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
  RemovedInstructions.insert(AI.getInstruction());
  recursivelyDeleteTriviallyDeadInstructions(AI.getInstruction(), true);
}


static void markAsNonAtomic(RefCountingInst *I) {
  I->setNonAtomic();
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

/// \return true of the given container is known to be a unique copy of the
/// array with no aliases. Cases we check:
///
/// (1) An @inout argument.
///
/// (2) A local variable, which may be copied from a by-val argument,
/// initialized directly, or copied from a function return value. We don't
/// need to check how it is initialized here, because that will show up as a
/// store to the local's address.
bool RegionBasedNonAtomicRCTransformer::checkUniqueCowContainer(
    SILFunction *F, SILValue CowContainer) {
  // Obtain the RC root of the container.
  SILValue Op = stripUniquenessPreservingCastsAndProjections(CowContainer);
  auto Root = RCIFI->getRCIdentityRoot(Op);

  if (isa<AllocStackInst>(Root))
    return true;

  SILArgument *Arg = dyn_cast<SILArgument>(Root);
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
  auto RCRoot = RCIFI->getRCIdentityRoot(
      stripUniquenessPreservingCastsAndProjections(Value));
  if (RCRoot == CowStruct)
    return true;
  auto *CowLoad = dyn_cast<LoadInst>(RCRoot);
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
#if 0
    assert(isUniqueArg(CowStruct) &&
           "Only COW objects passed as inout may have address types");
#endif
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

/// Returns true, if a given type is a COW type.
static CanType getCOWType(CanType Ty, SILModule &M) {
  // Strip of metatypes.
  while(auto MetaTy = dyn_cast<AnyMetatypeType>(Ty)) {
    Ty = MetaTy->getInstanceType()->getCanonicalType();
  }
#if 1
  // TODO: In the future, all COW types may conform
  // to a special COW protocol. In that case, simply
  // check if a type conforms to this protocol.
  auto COWProto =
      M.getASTContext().getProtocol(KnownProtocolKind::COW);

  if (COWProto) {
    // Find the conformance of the value type to COW protocol.
    // Check whether the type conforms to COW protocol.
    auto conformance =
        M.getSwiftModule()->lookupConformance(Ty, COWProto, nullptr);
    if (conformance.hasValue())
      return Ty;
  }
  return CanType();
#else
  // Check against a whitelist of COW types.
  auto CanTy = Ty.getDecl();
  if (M.getASTContext().getArrayDecl() == CanTy)
    return true;
  if (M.getASTContext().getDictionaryDecl == CanTy)
    return true;
  if (M.getASTContext().getSetDecl == CanTy)
    return true;
  return false;
#endif
}

static CanType getCOWType(SILType Ty, SILModule &M) {
  return getCOWType(Ty.getSwiftRValueType(), M);
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
  if (!Dest->getType().getObjectType().isHeapObjectReferenceType() &&
      !getCOWType(Dest->getType(), CowStruct->getParentBB()->getModule()))
    return false;

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
void RegionBasedNonAtomicRCTransformer::scanAllBlocks(UniquenessDataflow &DF) {
  // Unique/non-atomic function parameters are in
  // the IN set of the entry block.
  for (auto Arg : F->getArguments()) {
    if (isUniqueArg(Arg)) {
      assert(CowValueId.count(Arg) && "Unregistered CowValue");
      auto Id = CowValueId[Arg];
      DF.getBlockState(&*F->begin()).In[Id] = true;
      DEBUG(llvm::dbgs() << "Adding a unique parameter into IN set of the "
                            "entry basic block: ";
            Arg->dump());
    }
  }

  for (auto &BB : *F) {
    scanBasicBlock(&BB, DF);
  }
}

// Get a set of apply arguments that may alias a given COW value.
// Returns true, if there is at least one aliasing argument.
// TODO: Use escape analysis here? Similar to 
// AliasAnalysis::canApplyDecrementRefCount 
bool RegionBasedNonAtomicRCTransformer::getCowValueArgsOfApply(
    FullApplySite AI, SILValue CowValue, SmallVectorImpl<int> &Args,
    SmallVectorImpl<bool> &IsIndirectParam) {
  if (!AI.getInstruction())
    return true;
  DEBUG(llvm::dbgs() << "Analyzing if the following apply instruction is a candidate:\n";
        AI.getInstruction()->dumpInContext());
  bool Result = false;
  for (unsigned i = 0, e = AI.getArguments().size(); i < e; ++i) {
    // TODO: Use EscapeAnalysis to check if a given CowValue can escape into the
    // Arg.
    // TODO: Use EscapeAnalysis to check if a given Arg can escape inside the
    // function.
    // TODO: If EA is not available for a given function (e.g. its body is not
    // available), assume the worst case, i.e. the value would escape.
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
                                                        CandidateKind Kind,
                                                        RegionMode Mode) {
  Candidates.push_back(Candidate(I, CowValue, Kind, Mode));
  CandidateBBs.insert(I->getParent());
  DEBUG(llvm::dbgs() << "Mark as canidate:\n"; I->dumpInContext());
}

enum class COWOperation {
  // It is not an operation on a COW type.
  None,
  // Non-mutating operation on a COW type.
  NonMutating,
  // Mutating operation on COW a type.
  Mutating,
  // Unknown operation on COW a type.
  Unknown,
};

/// Try to classify a given invocation as an invocation of an 
/// operation on a COW type. Returns COWOperation::None if it
/// is not an operation on a COW type or it is not known how
/// to classify it.
static COWOperation classifyOperationOnCowType(SILInstruction *I) {
  auto FAS = FullApplySite::isa(I);

  // Not an apply.
  if (!FAS)
    return COWOperation::None;

  // Does not have a self argument.
  if (!FAS.hasSelfArgument())
    return COWOperation::None;

  auto Self = FAS.getSelfArgument();
  auto SelfTy = Self->getType();

  // Bail if it is now a COW type.
  auto COWTy = getCOWType(SelfTy, I->getModule());
  if (!COWTy)
    return COWOperation::None;
  assert((COWTy.getStructOrBoundGenericStruct() ||
          COWTy.getEnumOrBoundGenericEnum()) &&
         "Only struct-based or enum-based COW types are supported");


  auto Callee = FAS.getCalleeFunction();

  // If the self argument is inout, it is a mutating operation.
  if (Callee->getLoweredFunctionType()->getSelfParameter().isIndirectInOut()) {
    // TODO: Not every mutating operation makes the COW object unique.
    // For example, the implementation of a make_unique may invoke some
    // other mutating functions, which do not make the whole COW object unique
    // on their own.
    // TODO: Check that it is a public function at the AST level. Public mutating
    // functions on a COW type are supposed to make it unique among other things.
    if (Callee->isPossiblyUsedExternally())
      return COWOperation::Mutating;
  }

  // If it is a constructor call, it is a mutating operation.
  // FIXME: It does not necessarily makes the buffer unique.
  // For example, array constructors taking an existing buffer do not make
  // the object unique.
  if (isa<AnyMetatypeType>(SelfTy.getSwiftRValueType())) {
    // Constructors are supposed to return the objects of a COW type.
    auto ResultTy = Callee->getLoweredFunctionType()->getSILResult();
    auto ResultCOWTy = getCOWType(ResultTy, I->getModule());
    if (ResultCOWTy == COWTy) {
      // This is a constructor.
      // TODO: Some constructors do not make an object automatically unique.
      // May be return COWOperation::None in this case?
      return COWOperation::Mutating;
    }
  }

  // If any of non-self arguments are inout, we don't know what it is.
  // It may mutate those parameters.
  auto Params = Callee->getLoweredFunctionType()->getParameters();
  for (unsigned ArgIdx = 0, ArgEnd = Params.size(); ArgIdx != ArgEnd;
       ++ArgIdx) {
    if (Params[ArgIdx].isIndirectInOut())
      return COWOperation::Unknown;
  }

  return COWOperation::NonMutating;
}

/// Tries to find a successor BB taken when the value of the conditional
/// is true in the following code patterns:
/// %u = is_unique %v
/// %e = builtin "int_expect_Int1" (%u, %const)
/// cond_br %e, true_bb, false_bb
/// NOTE: The builtin "int_expect_Int1" is optional.
///
/// TODO: This is a workaround we need until we introduce is_unique_br
/// instruction.
static SILBasicBlock *findTrueSuccessor(SILInstruction *I) {
  assert(I->getType() == SILType::getBuiltinIntegerType(1, I->getModule().getASTContext()) &&
         "Expected Builtin.Int1");
  if (!I->hasOneUse())
    return nullptr;
  auto User = I->use_begin()->getUser();
  if (auto BI = dyn_cast<BuiltinInst>(User)) {
    // Check that it is a int_expect_Int1
    if (BI->getName().str() != "int_expect_Int1")
      return nullptr;
    if (!BI->hasOneUse())
      return nullptr;
    User = BI->use_begin()->getUser();
  }
  if (auto CBI = dyn_cast<CondBranchInst>(User)) {
    return CBI->getTrueBB();
  }
  return nullptr;
}

/// Returns true if a function is semantically a make
/// unique function, i.e. it only makes a COW object
/// unique if it is not unique yet. It should not have
/// any further side-effects.
static bool isMakeUniqueFunction(SILFunction *F) {
  // Check that this function only has a form:
  // bb0:
  // %u = is_unique %ptr
  // cond_br %u, bbTrue, bbFalse
  // bbTrue:
  //  br bbMerge
  // bbFalse:
  //  ...
  // bbMerge:
  // return
  return false;
}

///  Analysis functions

void RegionBasedNonAtomicRCTransformer::scanStoreInst(StoreInst *SI,
                                                      ScanState &S) {
  bool isAliasingDest = false;
  // Check if this instruction may store into a memory location
  // aliasing the location where array buffer reference is stored.
  // TODO: Check the new value. If the new value is known to be
  // unique/thread-local, there is no need to kill the current region.
  auto Dest = SI->getDest();

  // Check if it kills any non-local region.
  for (auto &KV : CowValueId) {
    auto CowValue = KV.getFirst();
    auto Id = KV.getSecond();
    if (isStoreAliasingCowValue(CowValue, Dest)) {
      // This is a kill.
      S.LastSeenOp[Id] = Kill;
      S.KilledCowValues[Id] = true;
      isAliasingDest = true;
      markAsCandidate(SI, CowValue, CANDIDATE_STORE_DEST, Mode);
      DEBUG(llvm::dbgs() << "\nKill operation for CowValue\n"
                         << CowValue;
            SI->dumpInContext());
      break;
    }
  }

  if (isAliasingDest)
    return;

  // Check if this instruction may store one of the tracked CowValues
  // somewhere. In this case, the buffer becomes non-unique.
  // It may still be thread-local, if the value does not escape.
  auto Src = SI->getSrc();

  // if (!Src->getType().getObjectType().isHeapObjectReferenceType() &&
  //    !getCOWType(Src->getType(), I->getModule()))
  //  continue;

  // TODO: Source could be a SIL value which contains a reference contained in
  // a COW value. If this reference would escape through this assignment,
  // the region should stop here.
  for (auto &KV : CowValueId) {
    auto CowValue = KV.getFirst();
    auto Id = KV.getSecond();
    if (isCowValue(CowValue, Src)) {
      // This is a kill.
      S.LastSeenOp[Id] = Kill;
      S.KilledCowValues[Id] = true;
      markAsCandidate(SI, CowValue, CANDIDATE_STORE_SRC, Mode);
      DEBUG(llvm::dbgs() << "\nKill operation for CowValue\n"
                         << CowValue;
            SI->dumpInContext());
      break;
    }
  }
}

void RegionBasedNonAtomicRCTransformer::scanApplyInst(FullApplySite AI,
                                                      ScanState &S) {
  DEBUG(llvm::dbgs() << "\nScan apply instruction:\n";
        AI.getInstruction()->dumpInContext());
  auto CowTypeOperationKind = classifyOperationOnCowType(AI.getInstruction());
  if (CowTypeOperationKind == COWOperation::Mutating) {
    // Any mutating operation on COW type makes it unique.
    // This is a GEN operation, it starts a region.
    // FIXME: Some constructors take an existing buffer as parameters
    // and do not produce a unique COW value.
    auto CowValue = AI.getSelfArgument();
    // It is a constructor.
    if (isa<AnyMetatypeType>(CowValue->getType().getSwiftRValueType())) {
      CowValue = AI.getInstruction();
      // Skip if we are not tracking this COWValue.
      if (!CowValueId.count(CowValue)) {
        DEBUG(llvm::dbgs() << "Skip a call of a static method on a non-tracked COW value\n");
        return;
      }
    }

    CowValue = RCIFI->getRCIdentityRoot(
        stripUniquenessPreservingCastsAndProjections(CowValue));
    assert(CowValueId.count(CowValue) && "Unregistered CowValue");
    S.LastSeenOp[CowValueId[CowValue]] = Gen;
    markAsCandidate(AI.getInstruction(), CowValue, CANDIDATE_GEN, Mode);

    DEBUG(llvm::dbgs() << "\nGen operation for CowValue\n"
                       << CowValue;
          AI.getInstruction()->dumpInContext());

    return;
  }

  // TODO: Special handling for checks like
  // ArrayCallKind::kArrayPropsIsNativeTypeChecked

  if (CowTypeOperationKind == COWOperation::NonMutating) {
    DEBUG(llvm::dbgs() << "Skip a non-mutating operation on a COW value\n");
    return;
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

  // Check if it kills any region.
  for (auto &KV : CowValueId) {
    auto CowValue = KV.getFirst();
    auto Id = KV.getSecond();
    SmallVector<int, 8> Args;
    SmallVector<bool, 4> IsIndirectParam;

    auto hasAliases =
        getCowValueArgsOfApply(AI, CowValue, Args, IsIndirectParam);
    if (Args.empty() || !hasAliases) {
      DEBUG(llvm::dbgs() << "None of the apply arguments alias any tracked COW values\n");
      continue;
    }
    for (auto Arg : Args) {
      if (Arg < 0)
        continue;
      // If an argument aliases a CowValue, mark the call instruction
      // as a candiate.
      auto isIndirect = IsIndirectParam[Arg];
      if (EA->canParameterEscape(AI, Arg, isIndirect)) {
        S.LastSeenOp[Id] = Kill;
        S.KilledCowValues[Id] = true;
        markAsCandidate(AI.getInstruction(), CowValue, CANDIDATE_KILL, Mode);
        DEBUG(llvm::dbgs() << "\nKill operation for CowValue:\n"
                           << CowValue;
              AI.getInstruction()->dumpInContext());
        // If the address of a COW value escapes, then we cannot
        // assum the uniqueness/thread-locality of this COW value
        // anymore after this point, because the value can be modified
        // by a different thread at any point. Even if we would see
        // a mutating operation on the COW value, we cannot assume as
        // usual that it made the object unique/thread-local.

        // Insert this CowValue into the KILL set.
        // Exclude it from the GEN set.
        S.EscapedCowValues[Id] = true;
        break;
      }
    }
  }
}

void RegionBasedNonAtomicRCTransformer::scanDeallocStackInst(
    DeallocStackInst *DSI, ScanState &S) {
  auto Val = DSI->getOperand();

  // Check if it kills any non-local region.
  for (auto &KV : CowValueId) {
    auto CowValue = KV.getFirst();
    auto Id = KV.getSecond();
    if (Val == CowValue) {
      // This is a kill.
      S.LastSeenOp[Id] = Kill;
      S.KilledCowValues[Id] = true;
      markAsCandidate(DSI, CowValue, CANDIDATE_KILL, Mode);
      DEBUG(llvm::dbgs() << "\nKill operation for CowValue\n"
                         << CowValue;
            DSI->dumpInContext());
      break;
    }
  }
}

void RegionBasedNonAtomicRCTransformer::scanIsUniqueInst(SILInstruction *I,
                                                     ScanState &S) {
  assert(isa<IsUniqueInst>(I) || isa<IsUniqueOrPinnedInst>(I));

  SILValue Op = stripUniquenessPreservingCastsAndProjections(I->getOperand(0));
  auto Root = RCIFI->getRCIdentityRoot(Op);
  DEBUG(llvm::dbgs() << "Found is_unique: "; I->dump();
        llvm::dbgs() << "\n"
                     << "RCRoot = " << Root << "\n");

  for (auto &KV : CowValueId) {
    auto CowValue = KV.getFirst();
    if (Root == CowValue) {
      markAsCandidate(I, CowValue, CANDIDATE_UNIQUE, UNIQUENESS_REGIONS);
      if (auto TrueBB = findTrueSuccessor(I)) {
        // The CowValue is unique at the beginning
        // of the TrueBB.
        auto Id = KV.getSecond();
        if (TrueBB->getTerminator() == &*TrueBB->begin() &&
            isa<BranchInst>(TrueBB->getTerminator())) {
          auto MergeBB = cast<BranchInst>(TrueBB->getTerminator())->getDestBB();
#if 0
              // This assert is wrong. Sometimes there could be more
              // than 2 predecessors.
              assert(std::distance(MergeBB->pred_begin(), MergeBB->pred_end()) == 2 &&
                     "Two predecessors are expected");
#endif
          for (auto Pred : MergeBB->getPreds())
            S.DF.getBlockState(Pred).Gen[Id] = true;
        }
      }
      break;
    }
  }
}

void RegionBasedNonAtomicRCTransformer::scanRefCountingInst(RefCountingInst *RC,
                                                            ScanState &S) {
  auto Ref = RC->getOperand(0);
  for (auto &KV : CowValueId) {
    auto CowValue = KV.getFirst();
    // Check if it kills any non-local region.
    // TODO: Retain/Release do not automatically kill
    // the thread-local property, but they kill the
    // uniqueness property. Retain can never kill
    // a thread-local region. For releases which are not non-final,
    // we need to ask the EA if the value would escape through
    // a destructor or could be changed via a destructor.
    // If this is a case, it should mark the end of the region.
    if (isRCofCowValueAt(CowValue, RC)) {
      if (Mode == UNIQUENESS_REGIONS) {
        // If this instruction may affect a reference count
        // of the CowValue (or any of its components),
        // then we pessimistically assume that it ends the
        // uniqueness region.
        if (isa<StrongRetainInst>(RC) || isa<RetainValueInst>(RC) ||
            isa<StrongReleaseInst>(RC) || isa<ReleaseValueInst>(RC))
          markAsCandidate(RC, CowValue, CANDIDATE_KILL, Mode);
      }
      if (Mode == THREAD_LOCAL_REGIONS) {
        markAsCandidate(RC, CowValue, CANDIDATE_RC, Mode);
      }
      return;
    }
  }

  // The RC operation is on a value which is not directly related
  // to any of the tracked COW values.
  // If this RC operatiom may result in a destructor call, it may
  // kill any of the tracked COW values, whose origin is unknown
  // (e.g. they are @inout arguments of a function or loaded from
  // a heap object).
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
// TODO: Current version relies on @_semantics attributes which may
// be eliminated in the future versions of the compiler. More over,
// these annotations are lost once a function with such an attribute
// is inlined. Therefore, currently this pass works only if it is
// invoked before inlining as after inlining all the attributes are lost.
// This limitation is rather unfortunate, because it would make more
// sense to run this pass pretty late in the pipeline after all the
// ARC optimization passes, which would eliminate most of the RC
// instructions.
void RegionBasedNonAtomicRCTransformer::scanBasicBlock(SILBasicBlock *BB,
                                                       UniquenessDataflow &DF) {
  // Remember if the last thing for a given CowValue
  // was kill or set.
  // Maps the CowValue to the last seen operation,
  // which is either set or kill.
  //
  ScanState S(DF);

  auto II = BB->begin();
  while (II != BB->end()) {
    auto I = &*II++;

    // TODO: Generalize for any COW types, not only arrays.
    // Check if instruction may overwrite the array buffer reference in the
    // container.
    if (auto *SI = dyn_cast<StoreInst>(I)) {
      scanStoreInst(SI, S);
      continue;
    }

    if (auto AI = FullApplySite::isa(I)) {
      scanApplyInst(AI, S);
      continue;
    }

    if (auto *DSI = dyn_cast<DeallocStackInst>(I)) {
      scanDeallocStackInst(DSI, S);
      continue;
    }

    if (isa<IsUniqueInst>(I) ||
        // Does pinned mean unique???
        isa<IsUniqueOrPinnedInst>(I)) {
      scanIsUniqueInst(I, S);
      continue;
    }

    if (auto *RC = dyn_cast<RefCountingInst>(I)) {
      scanRefCountingInst(RC, S);
      continue;
    }
    // Nothing else can affect uniqueness or thread-locality.
    continue;
  }

  // Initialize Gen, Kill and Out sets for the current BB.
  auto &BBState = DF.getBlockState(BB);

  for (unsigned i = 0, e = S.LastSeenOp.size(); i < e; ++i) {
    // Remember only those GEN instructions that are not followed
    // by a KILL, which means that they will be in the OUT set of this BB.
    if (S.LastSeenOp[i] == Gen)
      BBState.Gen[i] = true;
  }

  // If a value has escaped, it should not be present in the GEN set.
  for (auto i = S.EscapedCowValues.find_first(); i != -1;
       i = S.EscapedCowValues.find_next(i)) {
    BBState.Gen[i] = false;
  }

  // Initialize OUT sets with GEN sets.
  BBState.Out = BBState.Gen;


  for (auto i = S.KilledCowValues.find_first(); i != -1;
       i = S.KilledCowValues.find_next(i)) {
    BBState.Kill[i] = true;
  }
}

///  Transformation functions

void RegionBasedNonAtomicRCTransformer::transformStoreInst(StoreInst *SI,
                                                           TransformState &S) {
  auto CowValue = S.C->CowValue;

  assert(S.Kind == CandidateKind::CANDIDATE_STORE_DEST ||
         S.Kind == CandidateKind::CANDIDATE_STORE_SRC);
  assert(S.CowValue);

  auto Id = CowValueId[S.CowValue];

  if (S.Kind == CandidateKind::CANDIDATE_STORE_DEST) {
    DEBUG(llvm::dbgs() << "Kill operation for CowValue\n"
                       << CowValue;
          SI->dumpInContext());
    // The region is not active anymore after this point.
    S.CurrentlyActive[Id] = false;
    DEBUG(llvm::dbgs() << "end uniqueness region for: " << CowValue << "\n"
                       << "at instruction: ";
          SI->dump());
    return;
  }

  // This is a store of a CowValue into a different location,
  // which may create an alias.

  // This is a kill.
  S.CurrentlyActive[Id] = false;
  DEBUG(llvm::dbgs() << "end uniqueness region for: " << S.CowValue << "\n"
                     << "at instruction: ";
        SI->dump());
}

void RegionBasedNonAtomicRCTransformer::transformApplyInst(FullApplySite AI,
                                                      TransformState &S) {
  if (S.Kind == CandidateKind::CANDIDATE_KILL) {
    // Check whose uniqueness is changed.
    auto Id = CowValueId[S.CowValue];
    S.CurrentlyActive[Id] = false;
    S.EscapedCowValues[Id] = true;
    DEBUG(llvm::dbgs() << "End uniqueness region for: " << S.CowValue << "\n"
                       << "at instruction: ";
          S.I->dump());
    return;
  }

  if (S.Kind == CandidateKind::CANDIDATE_GEN) {
    // Check whose uniqueness is changed.
    auto Id = CowValueId[S.CowValue];

    if (S.Mode == THREAD_LOCAL_REGIONS) {
      if (AI.hasSelfArgument()) {
        auto *Callee = AI.getCalleeFunction();
        // Check if Self is currently unique.
        if (S.CurrentlyActive.test(Id) &&
            Callee->hasSemanticsAttr("generate.nonatomic")) {
          DEBUG(llvm::dbgs() << "Non-atomic version of the call can be used:\n";
                AI.getInstruction()->dumpInContext());
          replaceByNonAtomicApply(AI);
          S.Changes =
              StateChanges(S.Changes | SILAnalysis::InvalidationKind::Calls);
        }
      }
    }

    if (!S.CurrentlyActive[Id]) {
      S.CurrentlyActive[Id] = true;
      DEBUG(llvm::dbgs() << "Start uniqueness region for: " << S.CowValue
                         << "\n"
                         << "at instruction: ";
            S.I->dump());
    }
    return;
  }
  llvm_unreachable("Unknown kind of transformation candidate");
}

void RegionBasedNonAtomicRCTransformer::transformDeallocStackInst(
    DeallocStackInst *DSI, TransformState &S) {
  // End of a uniqueness region.
  assert(S.Kind == CandidateKind::CANDIDATE_KILL);
  assert(CowValueId.count(S.CowValue) && "Unregistered CowValue");
  auto Id = CowValueId[S.CowValue];
  S.CurrentlyActive[Id] = false;
  DEBUG(llvm::dbgs() << "End uniqueness region for: " << S.CowValue << "\n"
                     << "at instruction: ";
        S.I->dump());
}

void RegionBasedNonAtomicRCTransformer::transformIsUniqueInst(SILInstruction *I,
                                                     TransformState &S) {
  assert(isa<IsUniqueInst>(I) || isa<IsUniqueOrPinnedInst>(I));
  assert(S.Kind == CandidateKind::CANDIDATE_UNIQUE);
  assert(CowValueId.count(S.CowValue) && "Unregistered CowValue");
  auto Id = CowValueId[S.CowValue];
  if (!S.CurrentlyActive[Id])
    return;
  SILValue Op = stripUniquenessPreservingCastsAndProjections(I->getOperand(0));
  auto Root = RCIFI->getRCIdentityRoot(Op);
  DEBUG(llvm::dbgs() << "Found is_unique: "; I->dump();
        llvm::dbgs() << "\n"
                     << "RCRoot = " << Root << "\n");

  // The result of this check will be always true, because
  // it is inside a uniqueness region.
  SILBuilderWithScope B(I);
  auto boolTy =
      SILType::getBuiltinIntegerType(1, I->getModule().getASTContext());
  auto yes = B.createIntegerLiteral(I->getLoc(), boolTy, 1);
  DEBUG(llvm::dbgs() << "Replace " << SILValue(I) << " by " << SILValue(yes)
                     << "\n");
  RemovedInstructions.insert(I);
  I->replaceAllUsesWith(yes);
  I->eraseFromParent();
  S.Changes =
      StateChanges(S.Changes | SILAnalysis::InvalidationKind::Instructions);
}

void RegionBasedNonAtomicRCTransformer::transformRefCountingInst(
    RefCountingInst *RC, TransformState &S) {
  assert((S.Mode == THREAD_LOCAL_REGIONS &&
          S.Kind == CandidateKind::CANDIDATE_RC) ||
         (S.Mode == UNIQUENESS_REGIONS &&
          S.Kind == CandidateKind::CANDIDATE_KILL));
  assert(CowValueId.count(S.CowValue) && "Unregistered CowValue");
  // If the region for a given CowValue is active and
  // if this is the array buffer reference or if this is
  // the array container itself, then it can be replaced
  // by a non-atomic variant.
  auto Id = CowValueId[S.CowValue];
  if (S.CurrentlyActive.test(Id)) {
    if (S.Kind == CandidateKind::CANDIDATE_RC) {
      S.Changes =
          StateChanges(S.Changes | SILAnalysis::InvalidationKind::Instructions);
      markAsNonAtomic(RC);
      DEBUG(llvm::dbgs() << "RC operation inside make_mutable region can be "
                            "non-atomic: ";
            RC->dump());
    }

    if (S.Kind == CandidateKind::CANDIDATE_KILL) {
      // The region is not active anymore after this point.
      S.CurrentlyActive[Id] = false;
      DEBUG(llvm::dbgs() << "end uniqueness region for: " << S.CowValue << "\n"
                         << "at instruction: ";
            S.I->dump());
    }
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
//
// TODO: Currently this function makes use of @_semantics annotations.
// It would be nice to get rid of it. But this could be a bit problematic.
// For example, while it is clear that any public mutating function makes
// COW object unique, it is not clear if this is the only effect that it
// has. And for non-public mutating function it is not even clear if they
// make the object unique. It may happen that only a sequence of non-public
// mutating calls makes an object unique.
StateChanges
RegionBasedNonAtomicRCTransformer::transformAllBlocks(RegionMode Mode) {
  DEBUG(llvm::dbgs() << "** Transform basic blocks inside " << F->getName()
                     << " **\n");

  UniquenessDataflow &DF = (Mode == UNIQUENESS_REGIONS) ? UniquenessDF : ThreadLocalDF;

  SILBasicBlock *LastBB = nullptr;
  BlockState *BBState = nullptr;

  TransformState S;
  S.Changes = SILAnalysis::InvalidationKind::Nothing;
  S.Mode = Mode;
  S.EscapedCowValues.resize(DF.getStateLength());

  // Visit all candiate instructions.
  // Candidate instructions inside a basic block are visited
  // in the order of their execution.
  for (auto &C : Candidates) {
    S.C = &C;
    // Skip any unrelated candidates.
    if (C.Mode != Mode)
      continue;
    // Skip removed instructions.
    if (RemovedInstructions.count(C.I))
      continue;
    S.I = C.I;
    S.CowValue = C.CowValue;
    assert(CowValueId.count(S.CowValue) && "Unregistered CowValue");
    auto *BB = S.I->getParent();
    S.Kind = C.Kind;

    // If a value has escaped in the current BB, no new region can be started in
    // the current BB after that point.
    if (BB == LastBB && S.Kind == CANDIDATE_GEN &&
        S.EscapedCowValues[CowValueId[S.CowValue]])
      continue;

    if (BB != LastBB) {
      // If candidates from a given block are not adjacent
      // to each other, we may need to store the updated state.
      if (LastBB)
        DF.getBlockState(LastBB).In = S.CurrentlyActive;
      // Initialize a state for the current block.
      BBState = &DF.getBlockState(BB);
      S.CurrentlyActive = BBState->In;
      S.EscapedCowValues.reset();
    }
    LastBB = BB;

    DEBUG(llvm::dbgs() << "\n** Transform a candidate instruction:\n";
          S.I->dumpInContext());

    if (auto *RC = dyn_cast<RefCountingInst>(S.I)) {
      transformRefCountingInst(RC, S);
      continue;
    }

    // Check if instruction may overwrite the array buffer reference in the
    // container.
    if (auto *SI = dyn_cast<StoreInst>(S.I)) {
      transformStoreInst(SI, S);
      continue;
    }

    if (auto AI = FullApplySite::isa(S.I)) {
      transformApplyInst(AI, S);
      continue;
    }

    if (Mode == UNIQUENESS_REGIONS) {
      if (isa<IsUniqueInst>(S.I) || isa<IsUniqueOrPinnedInst>(S.I)) {
        transformIsUniqueInst(S.I, S);
      }
      continue;
    }

    if (auto *DSI = dyn_cast<DeallocStackInst>(S.I)) {
      transformDeallocStackInst(DSI, S);
      continue;
    }

    // Nothing else can change or escape the array buffer reference.
    llvm::dbgs() << "Unexpected candidate was found:\n";
    S.I->dumpInContext();
    llvm::dbgs() << "\n";
    llvm_unreachable("Unexpected candidate was found");
  }
  return S.Changes;
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

static bool isValueOfUniqueReferenceType(SILValue CowValue,
                                         SILInstruction *I) {
  auto COWTy = getCOWType(CowValue->getType(), I->getModule());
  if (COWTy)
    return true;
  // TODO: Once we can mark "unique" fields, check that I is accessing
  // such a field of a unique type.
  // But for now assume that anything checked by an is_unique instruction
  // is interesting.
  return true;
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
  // Find all distict SILValues, which are potential unique/thread-local COW
  // objects. This gives us the number of differrent CowValues which are made
  // unique in the current function.
  for (SILBasicBlock &BB : *F) {
    for (auto Iter = BB.begin(); Iter != BB.end();) {
      SILInstruction *I = &*Iter++;

      if (isa<IsUniqueInst>(I) || isa<IsUniqueOrPinnedInst>(I)) {
        SILValue Op =
            stripUniquenessPreservingCastsAndProjections(I->getOperand(0));
        auto CowValue = RCIFI->getRCIdentityRoot(Op);
        // Check of the root is a COW value.
        if (isValueOfUniqueReferenceType(CowValue, I)) {
          DEBUG(llvm::dbgs() << "Found an is_unique on a COW type:\n";
                I->dumpInContext());
          if (!CowValueId.count(CowValue)) {
            CowValueId[CowValue] = UniqueIdx++;
            IdToCowValue.push_back(CowValue);
          }
        }
        continue;
      }

      // TODO: Check for non-escaping Cow Containers like
      // local variables and by-value arguments? Or let it
      // be handled by the non-region-based non-atomic-rc pass?

      if (!isa<ApplyInst>(I)) {
        continue;
      }

      auto COWOperationKind = classifyOperationOnCowType(I);
      if (COWOperationKind != COWOperation::Mutating)
        continue;

      DEBUG(llvm::dbgs() << "Found a mutating operation on a COW type:\n";
            I->dumpInContext());

      auto FAS = FullApplySite::isa(I);

      if (FAS && FAS.hasSelfArgument() &&
          checkUniqueCowContainer(F, FAS.getSelfArgument())) {
        // Add to the set of makeUnique calls
        // The COW object that is made a thread-local by this call.
        SILValue Op =
            stripUniquenessPreservingCastsAndProjections(FAS.getSelfArgument());
        auto CowValue = RCIFI->getRCIdentityRoot(Op);

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

static void dumpValueIdMapping(StringRef title,
                               llvm::DenseMap<SILValue, unsigned> &CowValueId) {
  llvm::dbgs() << title << "\n";
  for (auto &KV : CowValueId) {
    llvm::dbgs() << KV.second << " <== " << KV.first << "\n";
  }
}

void RegionBasedNonAtomicRCTransformer::computeUniqenesssRegions() {
  Mode = UNIQUENESS_REGIONS;
  UniquenessDF.initStates(CowValueId.size());
  // Find the places where regions end.
  scanAllBlocks(UniquenessDF);
  // Perform a datafow analysis to find out the span
  // of each region.
  DEBUG(dumpValueIdMapping("Mapping after computeUniqenesssRegions", CowValueId));
  UniquenessDF.compute();
}

void RegionBasedNonAtomicRCTransformer::computeThreadLocalRegions() {
  Mode = THREAD_LOCAL_REGIONS;
  ThreadLocalDF.initStates(CowValueId.size());
  // Find the places where regions end.
  scanAllBlocks(ThreadLocalDF);
  // Perform a datafow analysis to find out the span
  // of each region.
  DEBUG(dumpValueIdMapping("Mapping after computeThreadLocalRegions", CowValueId));
  ThreadLocalDF.compute();
}

StateChanges RegionBasedNonAtomicRCTransformer::processUniqenessRegions() {
  // Identify the beginning of all uniqueness regions.
  findAllMakeUnique();
  DEBUG(dumpValueIdMapping("Mapping after findAllMakeUnique:", CowValueId));
  // Bail if there are now COW values to be tracked.
  if (CowValueId.empty())
    return SILAnalysis::InvalidationKind::Nothing;

  computeUniqenesssRegions();
  computeThreadLocalRegions();

  // Now walk the regions and perform the transformations.
  auto ChangesUniquenss = transformAllBlocks(UNIQUENESS_REGIONS);
  auto ChangesThreadLocal = transformAllBlocks(THREAD_LOCAL_REGIONS);
  //auto ChangesThreadLocal = StateChanges::Nothing;
  auto Changes = StateChanges(ChangesUniquenss | ChangesThreadLocal);
  return Changes;
}

StateChanges RegionBasedNonAtomicRCTransformer::process() {
  DEBUG(llvm::dbgs() << "\nAbout to process function:\n"; F->dump());
  auto ChangesUniqueness = processUniqenessRegions();

  if (ChangesUniqueness) {
    DEBUG(llvm::dbgs() << "\n\nFunction after the transformation:"; F->dump());
  }

  return StateChanges(ChangesUniqueness);
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
