//===-------  NonAtomicRC.cpp - Use non-atomic reference counting  -------===//
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

#define DEBUG_TYPE "non-atomic-rc"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "swift/SILOptimizer/Analysis/ArraySemantic.h"
#include "swift/SILOptimizer/Analysis/DominanceAnalysis.h"
#include "swift/SILOptimizer/Analysis/EscapeAnalysis.h"
#include "swift/SILOptimizer/Analysis/RCIdentityAnalysis.h"
#include "swift/SIL/SILArgument.h"
#include "swift/SIL/SILBuilder.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"

STATISTIC(NumNonAtomicRC, "Number of non-atomic RC operations");

using namespace swift;

namespace {

  // Bitvector implementation to be used for the dataflow analysis.
  typedef llvm::SmallBitVector StateBitVector;

  llvm::raw_ostream &operator<<(llvm::raw_ostream &stream,
                                llvm::BitVector &BV) {
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
  int getBlockIdx(SILBasicBlock *BB) const { return BlockIds.lookup(BB);}
  unsigned getStateLength() const {return StateLength; }
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
  } while(Changed);
}

/// Helper function to dump the results of
/// the dataflow analysis.
void Dataflow::dump() {
  for (auto &BB : *F) {
    auto &BlockState = getBlockState(&BB);
    auto BBId = getBlockIdx(&BB);
    DEBUG(
    llvm::dbgs() << "\nDataflow results for BB " << BBId << ":\n";
    llvm::dbgs() << "In = " << BlockState.In << "\n";
    llvm::dbgs() << "Out = " << BlockState.Out << "\n";
    llvm::dbgs() << "Gen = " << BlockState.Gen << "\n";
    llvm::dbgs() << "Kill = " << BlockState.Kill << "\n";
    BB.dump()
    );
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

public:
  NonAtomicRCTransformer(SILFunction *F,
                         EscapeAnalysis::ConnectionGraph *ConGraph,
                         EscapeAnalysis *EA,
                         RCIdentityFunctionInfo *RCIFI)
      : F(F), ConGraph(ConGraph), EA(EA), RCIFI(RCIFI), DF(F) {}

  StateChanges process();

private:
  StateChanges processUniqenessRegions();
  StateChanges processNonEscapingRefCountingInsts();
  bool isEligableRefCountingInst(SILInstruction *I);
  StateChanges tryNonAtomicRC(SILInstruction *I);
  bool isArrayValue(ValueBase *ArrayStruct, SILValue Value);
  bool isRCofArrayValueAt(ValueBase *ArrayStruct, SILInstruction *Inst);
  bool isStoreAliasingArrayValue(ValueBase *ArrayStruct, SILValue Dest);
  void findAllMakeUnique();
  void scanAllBlocks();
  void scanBasicBlock(SILBasicBlock *BB);
  StateChanges transformAllBlocks();
  void getCowValueArgsOfApply(FullApplySite AI, SILValue CowValue, SmallVectorImpl<int> &Args);
  void markAsCandidate(SILInstruction *I);
}
;

/// Returns true, if a given array semantics call does not
/// change the uniqueness of the array buffer.
static bool doesNotChangeUniquness(ArraySemanticsCall &C) {
  switch (C.getKind()) {
  default: return false;
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
  auto Root = RCInst->getOperand(0).stripAddressProjections();
  auto *Node = ConGraph->getNodeOrNull(RCInst->getOperand(0), EA);
  if (!Node)
    return SILAnalysis::InvalidationKind::Nothing;

  // As long as the value does not escape the function, it is fine.
  if (Node->escapes())
    return SILAnalysis::InvalidationKind::Nothing;

  // This value does not escape, which means that it is
  // thread-local.
  // Use non-atomic RC instructions for it.
  RCInst->setNonAtomic(true);
  NumNonAtomicRC++;
  DEBUG(
    llvm::dbgs() << "Marking the RC instruction as non-atomic:\n";
    RCInst->dumpInContext();
    );
  return SILAnalysis::InvalidationKind::Instructions;
}

/// Is it an instruction that creates a uniquelly referenced
/// object?
static ArraySemanticsCall isMakeUniqueCall(SILInstruction *I) {
  ArraySemanticsCall Call(I);
  if (Call && Call.getKind() == ArrayCallKind::kMakeMutable)
    return Call;
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
bool checkUniqueArrayContainer(SILFunction *Function, SILValue ArrayContainer) {
  if (SILArgument *Arg = dyn_cast<SILArgument>(ArrayContainer)) {
    // Check that the argument is passed as an inout type. This means there are
    // no aliases accessible within this function scope.
    auto Params = Function->getLoweredFunctionType()->getParameters();
    ArrayRef<SILArgument*> FunctionArgs = Function->begin()->getBBArgs();
    for (unsigned ArgIdx = 0, ArgEnd = Params.size();
         ArgIdx != ArgEnd; ++ArgIdx) {
      if (FunctionArgs[ArgIdx] != Arg)
        continue;

      if (!Params[ArgIdx].isIndirectInOut()) {
        DEBUG(llvm::dbgs() << "    Skipping Array: Not an inout argument!\n");
        return false;
      }
    }
    return true;
  }
  else if (isa<AllocStackInst>(ArrayContainer))
    return true;

  DEBUG(llvm::dbgs()
        << "    Skipping Array: Not an argument or local variable!\n");
  return false;
}

bool NonAtomicRCTransformer::isArrayValue(ValueBase *ArrayStruct,
                                          SILValue Value) {
  auto Root = RCIFI->getRCIdentityRoot(Value);
  if (Root.getDef() == ArrayStruct)
    return true;
  auto *ArrayLoad = dyn_cast<LoadInst>(Root);
  if (!ArrayLoad)
    return false;

  if (ArrayLoad->getOperand().getDef() == ArrayStruct)
    return true;

  // Is it an RC operation on the buffer reference?
  if (RCIFI->getRCIdentityRoot(
               ArrayLoad->getOperand().stripAddressProjections())
          .getDef() == ArrayStruct)
    return true;

  return false;
}



/// Check that the array value stored in \p ArrayStruct is operand of this RC by
/// \Inst.
bool NonAtomicRCTransformer::isRCofArrayValueAt(ValueBase *ArrayStruct,
                                                SILInstruction *Inst) {
  auto *RCI = dyn_cast<RefCountingInst>(Inst);
  if (!RCI)
    return false;
  return isArrayValue(ArrayStruct, RCI->getOperand(0));
}

bool NonAtomicRCTransformer::isStoreAliasingArrayValue(ValueBase *ArrayStruct,
                                                       SILValue Dest) {
  auto Root = RCIFI->getRCIdentityRoot(Dest);

  // Is it overwriting the array struct?
  if (Root.getDef() == ArrayStruct)
    return true;

  // Is it a store to the buffer reference?
  // TODO: Make this check more precise?
  if (RCIFI->getRCIdentityRoot(Root.stripAddressProjections()).getDef() ==
      ArrayStruct)
    return true;

  return false;
}

void NonAtomicRCTransformer::scanAllBlocks() {
  for (auto &BB : *F) {
    scanBasicBlock(&BB);
  }
}

void NonAtomicRCTransformer::getCowValueArgsOfApply(FullApplySite AI, SILValue CowValue, SmallVectorImpl<int> &Args) {
  for (unsigned i = 0, e = AI.getArguments().size(); i < e; ++i) {
    auto Arg = AI.getArgument(i);
    if (isArrayValue(CowValue.getDef(), Arg))
      return Args.push_back(i);
  }
}

void NonAtomicRCTransformer::markAsCandidate(SILInstruction *I) {
  Candidates.insert(I);
  CandidateBBs.insert(I->getParent());
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
  enum Op {
    None,
    Gen,
    Kill
  };

  llvm::SmallVector<Op, 32> LastSeenOp;
  LastSeenOp.resize(DF.getStateLength());

  // Remember which CowValue regions were killed in this BB.
  StateBitVector KilledCowValues;
  KilledCowValues.resize(DF.getStateLength());

  auto II = BB->begin();
  while (II != BB->end()) {
    auto I = &*II++;

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
        if (isStoreAliasingArrayValue(CowValue.getDef(), Dest)) {
          // This is a kill.
          LastSeenOp[Id] = Kill;
          KilledCowValues[Id] = true;
          isAliasingDest = true;
          markAsCandidate(I);
          DEBUG(llvm::dbgs() << "Kill operation for CowValue\n" << CowValue;
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
        if (isArrayValue(CowValue.getDef(), Src)) {
          // This is a kill.
          LastSeenOp[Id] = Kill;
          KilledCowValues[Id] = true;
          markAsCandidate(I);
          DEBUG(llvm::dbgs() << "Kill operation for CowValue\n" << CowValue;
                I->dumpInContext());
          break;
        }
      }
      continue;
    }

    if (auto AI = FullApplySite::isa(I)) {
      ArraySemanticsCall ArrayCall(AI.getInstruction());
      if (ArrayCall && ArrayCall.getKind() == ArrayCallKind::kMakeMutable) {
        // Add to the set of makeUnique calls
        // The COW object that is made a thread-local by this call.
        auto CowValue = ArrayCall.getSelf();

        // TODO: Check if there is an existing region which is alive
        // and uses the same CowValue.If this is the case, this
        // make unique call can be just removed and ignored.
        LastSeenOp[CowValueId[CowValue]] = Gen;
        markAsCandidate(I);

        DEBUG(llvm::dbgs() << "Gen operation for CowValue\n" << CowValue;
              I->dumpInContext());

        continue;
      }

      // Check if this array semantics call takes one of the tracked
      // CowValues as its arguments.
      if (ArrayCall) {
        if (doesNotChangeUniquness(ArrayCall))
          continue;

#if 1
        // Check whose uniqueness is changed.
        for (auto &KV : CowValueId) {
          auto CowValue = KV.getFirst();
          auto Id = KV.getSecond();
          SmallVector<int, 8> Args;
          getCowValueArgsOfApply(AI, CowValue, Args);
          if (Args.size()) {
            DEBUG(llvm::dbgs() << "Kill operation for CowValue:\n" << CowValue;
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
      // TODO: We want an API to check if a given SILValue is an argument of a
      // apply site and if it is escaping inside the function.

      // Check if it kills any non-local region.
      for (auto &KV : CowValueId) {
        auto CowValue = KV.getFirst();
        auto Id = KV.getSecond();
        SmallVector<int, 8> Args;
        getCowValueArgsOfApply(AI, CowValue, Args);
        if (Args.empty())
          continue;
        for (auto Arg : Args) {
          auto FnTy = AI.getSubstCalleeType();
          auto isIndirect = FnTy->getParameters()[Arg].isIndirect();
          if (EA->canParameterEscape(AI, Arg, isIndirect)) {
            LastSeenOp[Id] = Kill;
            KilledCowValues[Id] = true;
            markAsCandidate(I);
            DEBUG(llvm::dbgs() << "Kill operation for CowValue:\n" << CowValue;
                  I->dumpInContext());
            break;
          }
        }
      }
      continue;
    }

    if (auto *DSI = dyn_cast<DeallocStackInst>(I)) {
      auto *Val = DSI->getOperand().getDef();

      // Check if it kills any non-local region.
      for (auto &KV : CowValueId) {
        auto CowValue = KV.getFirst();
        auto Id = KV.getSecond();
        if (Val == CowValue.getDef()) {
          // This is a kill.
          LastSeenOp[Id] = Kill;
          KilledCowValues[Id] = true;
          markAsCandidate(I);
          DEBUG(llvm::dbgs() << "Kill operation for CowValue\n" << CowValue;
                I->dumpInContext());
          break;
        }
      }
      continue;
    }

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
        if (isArrayValue(CowValue.getDef(), RCVal)) {
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

  for (unsigned i = 0, e = LastSeenOp.size(); i < e; ++i) {
    if (LastSeenOp[i] == Gen)
      DF.getBlockState(BB).Gen[i] = true;
  }

  for (auto i = KilledCowValues.find_first(); i != -1;
       i = KilledCowValues.find_next(i)) {
    DF.getBlockState(BB).Kill[i] = true;
  }
}

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

      // If this instruction is not marked as "interesting" during the scan phase, bail.
      if (Candidates.count(I))
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
          if (CurrentlyActive.test(Id) &&
              isRCofArrayValueAt(CowValue.getDef(), I)) {
            Changes = StateChanges( Changes | SILAnalysis::InvalidationKind::Instructions);
            RC->setNonAtomic(true);
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
          if (isStoreAliasingArrayValue(CowValue.getDef(), Dest)) {
            DEBUG(llvm::dbgs() << "Kill operation for CowValue\n" << CowValue;
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
          if (isArrayValue(CowValue.getDef(), Src)) {
            // This is a kill.
            CurrentlyActive[Id] = false;
            DEBUG(llvm::dbgs() << "Kill operation for CowValue\n" << CowValue;
                  I->dumpInContext());
            break;
          }
        }
        continue;
      }

      if (auto AI = FullApplySite::isa(I)) {
        ArraySemanticsCall ArrayCall(AI.getInstruction());
        if (ArrayCall && ArrayCall.getKind() == ArrayCallKind::kMakeMutable) {
          // Add to the set of makeUnique calls
          // The COW object that is made a thread-local by this call.
          auto CowValue = ArrayCall.getSelf();

          // Check if this make_mutable is inside an existing region for the
          // same CowValue. If this is the case, then it can be removed.
          // The region may have started either in this BB or outside.
          auto Id = CowValueId[CowValue];
          if (CurrentlyActive.test(Id)) {
            DEBUG(llvm::dbgs() << "make_mutable call can be eliminated:\n";
                  (*ArrayCall).dumpInContext());
            ArrayCall.removeCall();
            Changes = StateChanges( Changes | SILAnalysis::InvalidationKind::Calls);
            // TODO: Rescan the release instruction?
            continue;
          }

          // Mark region as active.
          CurrentlyActive[Id] = true;
          continue;
        }

        if (ArrayCall) {
          if (doesNotChangeUniquness(ArrayCall))
            continue;
          // Check whose uniqueness is changed.
          for (auto &KV : CowValueId) {
            auto CowValue = KV.getFirst();
            auto Id = KV.getSecond();
            SmallVector<int, 8> Args;
            getCowValueArgsOfApply(AI, CowValue, Args);
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
        // TODO: We want an API to check if a given SILValue is an argument of a
        // apply site and if it is escaping inside the function.

        // Check if it kills any non-local region.
        for (auto &KV : CowValueId) {
          auto CowValue = KV.getFirst();
          auto Id = KV.getSecond();
          SmallVector<int, 8> Args;
          getCowValueArgsOfApply(AI, CowValue, Args);
          if (Args.empty())
            continue;
          for (auto Arg : Args) {
            auto FnTy = AI.getSubstCalleeType();
            auto isIndirect = FnTy->getParameters()[Arg].isIndirect();
            if (EA->canParameterEscape(AI, Arg, isIndirect)) {
              // The region is not active anymore after this point.
              CurrentlyActive[Id] = false;
              break;
            }
          }
        }
        continue;
      }

      if (auto *DSI = dyn_cast<DeallocStackInst>(I)) {
        auto *Val = DSI->getOperand().getDef();

        for (auto &KV : CowValueId) {
          auto CowValue = KV.getFirst();
          auto Id = KV.getSecond();
          if (Val == CowValue.getDef()) {
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
/// TODO: Handle GENs followed by KILLs.
void NonAtomicRCTransformer::findAllMakeUnique() {
  unsigned UniqueIdx = 0;
  // Find all make_mutable. This gives us the number
  // of differrent CowValues which are made unique
  // in the function.
  for (SILBasicBlock &BB : *F) {
    SILInstruction *LastMatching = nullptr;
    for (auto Iter = BB.begin(); Iter != BB.end();) {
      SILInstruction *I = &*Iter++;
      if (!isa<ApplyInst>(I)) {
        continue;
      }
      auto Call = isMakeUniqueCall(I);
      if (Call && Call.getSelf() &&
          checkUniqueArrayContainer(F, Call.getSelf())) {
        // Add to the set of makeUnique calls
        // The COW object that is made a thread-local by this call.
        auto CowValue = Call.getSelf();
        DEBUG(llvm::dbgs() << "\nThe following onbject is made thread-local: "
                           << CowValue << "\n";
              llvm::dbgs() << " by the instruction:\n";
              I->dumpInContext());

        // Create a region for this cow value.
        // If we have seen a region for the same value already, we should
        // assign the same index to it.
        unsigned Id = 0;
        if (!CowValueId.count(CowValue)) {
          Id = UniqueIdx++;
          CowValueId[CowValue] = Id;
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
  // No instructions were changed in a way that requires reprocessing.
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
  DEBUG(llvm::dbgs() << "\nAbout to process function:\n";
        F->dump());
  auto ChangesUniquness = processUniqenessRegions();
  auto ChangesRefCounting = processNonEscapingRefCountingInsts();

  if (ChangesUniquness || ChangesRefCounting) {
    DEBUG(llvm::dbgs() << "Function after the transformation:";
          F->dump());
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
    DEBUG(llvm::dbgs() << "** NonAtomicRC **\n");

    auto *EA = PM->getAnalysis<EscapeAnalysis>();
    auto *RCIA = PM->getAnalysis<RCIdentityAnalysis>();

    SILFunction *F = getFunction();
    auto *ConGraph = EA->getConnectionGraph(F);
    if (ConGraph) {
      NonAtomicRCTransformer Transformer(F, ConGraph, EA, RCIA->get(F));
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
