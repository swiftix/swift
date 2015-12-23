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
#include "llvm/ADT/Statistic.h"

STATISTIC(NumNonAtomicRC, "Number of non-atomic RC operations");

using namespace swift;

//===----------------------------------------------------------------------===//
//                              Top Level Driver
//===----------------------------------------------------------------------===//

namespace {

  llvm::raw_ostream& operator<< (llvm::raw_ostream& stream, llvm::BitVector& BV) {
    unsigned size = BV.size();
    stream << "[ ";
    for (unsigned i = 0; i < size; ++i)
      stream << BV[i] << " ";
    stream << ']';
    return stream;
  }

// Region where a given object is unique and thread-safe.
class Region {
public:
  typedef SmallVector<SILInstruction *, 4> RegionEndPoints;

private:
  // The COW value tracked by this region
  SILValue CowValue;
  // Where the region starts.
  SILInstruction *StartPoint;
  // Where the region ends.
  RegionEndPoints EndPoints;

  llvm::DenseSet<SILBasicBlock *> LiveThrough;

  // The index of this region in the dataflow bit vectors.
  unsigned Id;

public:
  Region(SILInstruction *StartPoint, SILValue CowValue, unsigned Id)
      : CowValue(CowValue), StartPoint(StartPoint), Id(Id) {}

  SILValue getCowValue() const { return CowValue; }
  SILInstruction *getStartPoint() const { return StartPoint; }
  const RegionEndPoints &getEndPoints() const { return EndPoints; }
  unsigned getId() const { return Id; }

  void addEndPoint(SILInstruction *EndPoint) {
    EndPoints.push_back(EndPoint);
  }

  // true if the COW value maintains its property through this
  // basic block, i.e. it has this property on entry and on
  // exit to/from this basic block.
  bool isLiveThrough(SILBasicBlock *BB);
  // true if COW value maintains its property at this point.
  bool isLiveAt(SILInstruction *I);
};

// Representation of a BB state during the dataflow analysis.
// Bit vectors are indexed by the id of a COW value.
struct BlockState {
  llvm::BitVector In;
  llvm::BitVector Out;
  llvm::BitVector Gen;
  llvm::BitVector Kill;
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
  virtual llvm::BitVector mergePredecessorStates(SILBasicBlock *BB);
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

// Perform a logical AND on the OUT sets of all predecessors.
llvm::BitVector Dataflow::mergePredecessorStates(SILBasicBlock *BB) {
  if (BB->pred_empty())
    return getBlockState(BB).In;
  llvm::BitVector Result(getStateLength(), true);
  for (auto Pred : BB->getPreds()) {
    Result &= getBlockState(Pred).Out;
  }
  return Result;
}

void Dataflow::compute() {
  bool Changed;
  initStates();
  do {
    Changed = false;
    // Visit all BBs
    // TODO: Use a good order, so that definitions are always visited
    // before their uses.
    // Update the in/out sets.
    for (auto &BB : *F) {
      auto Idx = getBlockIdx(&BB);
      auto &BBState = getBlockState(&BB);
      auto NewIn = mergePredecessorStates(&BB);
      assert(NewIn.size() == getStateLength());
      if (NewIn == BBState.In)
        continue;
      Changed = true;
      BBState.In = NewIn;
      // Out = NewIn & Gen & ~Kill
      BBState.Out = NewIn;
      assert(BBState.Out.size() == getStateLength());
      BBState.Out |= BBState.Gen;
      assert(BBState.Out.size() == getStateLength());
      BBState.Out.reset(BBState.Kill);
      assert(BBState.Out.size() == getStateLength());
    }
  } while(Changed);
}

void Dataflow::dump() {
  for (auto &BB : *F) {
    auto &BlockState = getBlockState(&BB);
    auto BBId = getBlockIdx(&BB);
    llvm::dbgs() << "\nDataflow results for BB " << BBId << ":\n";
    llvm::dbgs() << "In = " << BlockState.In << "\n";
    llvm::dbgs() << "Out = " << BlockState.Out << "\n";
    llvm::dbgs() << "Gen = " << BlockState.Gen << "\n";
    llvm::dbgs() << "Kill = " << BlockState.Kill << "\n";

    BB.dump();
  }
}

// Customization of a general dataflow analysis
// for tracking the uniguqness.
class UniquenessDataflow : public Dataflow {
  ArrayRef<Region> Regions;
public:
  UniquenessDataflow(SILFunction *F) : Dataflow(F) {}

  void initStates() {
   for (auto &BBState : BlockStates) {
      BBState.In.resize(getStateLength(), true);
      BBState.Out.resize(getStateLength(), false);
      BBState.Gen.resize(getStateLength(), false);
      BBState.Kill.resize(getStateLength(), false);
    }

    // Entry block does not have any bits set for the In set.
    getBlockState(&*F->begin()).In.reset();

    // Initialize the Gen sets.
    for (auto &Region : Regions) {
      auto *RegionBB = Region.getStartPoint()->getParent();
      auto &BBState = getBlockState(RegionBB);
      BBState.Gen[Region.getId()] = true;
    }
  }

  void compute(ArrayRef<Region> Regions) {
    this->Regions = Regions;
    setStateLength(Regions.size());
    Dataflow::compute();
    dump();
    // Update regions using the resuls of the dataflow
    // analysis.
  }
};


class NonAtomicRCTransformer {
  SILFunction *F;
  EscapeAnalysis::ConnectionGraph *ConGraph;
  EscapeAnalysis *EA;
  RCIdentityFunctionInfo *RCIFI;

  SmallVector<Region, 8> Regions;
  UniquenessDataflow DF;
  llvm::DenseMap<SILValue, unsigned> CowValueId;


  bool isEligableRefCountingInst(SILInstruction *I);
  bool tryNonAtomicRC(SILInstruction *I);
  bool isRCofArrayValueAt(ValueBase *ArrayStruct, SILInstruction *Inst);
  bool isStoreAliasingArrayValue(ValueBase *ArrayStruct, SILValue Dest);
  SILInstruction *analyzeBB(SILValue ArrayContainer, SILInstruction *Start);
  void computeThreadSafeRegion(ArraySemanticsCall Call);
  void findAllMakeUnique();

public:
  NonAtomicRCTransformer(SILFunction *F,
                         EscapeAnalysis::ConnectionGraph *ConGraph,
                         EscapeAnalysis *EA,
                         RCIdentityFunctionInfo *RCIFI)
      : F(F), ConGraph(ConGraph), EA(EA), RCIFI(RCIFI), DF(F) {}

  bool process();
};

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
      Transformer.process();
    }
  }

  StringRef getName() override { return "NonAtomicRC"; }
};

bool NonAtomicRCTransformer::isEligableRefCountingInst(SILInstruction *I) {
  return isa<RefCountingInst>(I) && !cast<RefCountingInst>(I)->isNonAtomic();
}

bool NonAtomicRCTransformer::tryNonAtomicRC(SILInstruction *I) {
  assert(isa<RefCountingInst>(I));
  auto *RCInst = cast<RefCountingInst>(I);
  auto Root = RCInst->getOperand(0).stripAddressProjections();
  auto *Node = ConGraph->getNodeOrNull(RCInst->getOperand(0), EA);
  if (!Node)
    return false;

  // As long as the value does not escape the function, it is fine.
  if (Node->escapesInsideFunction(false))
    return false;

  // This value does not escape, which means that it is
  // thread-local.
  // Use non-atomic RC instructions for it.
  RCInst->setNonAtomic(true);
  NumNonAtomicRC++;
  llvm::dbgs() << "Marking the RC instruction as non-atomic:\n";
  RCInst->dumpInContext();
  return true;
}

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

/// Check that the array value stored in \p ArrayStruct is operand of this RC by
/// \Inst.
bool NonAtomicRCTransformer::isRCofArrayValueAt(ValueBase *ArrayStruct,
                                                SILInstruction *Inst) {
  auto *RCI = dyn_cast<RefCountingInst>(Inst);
  if (!RCI)
    return false;
  auto Root = RCIFI->getRCIdentityRoot(RCI->getOperand(0));
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

/// Analyze a basic block starting at the instruciton I.
/// Return the first instruction that may overwrite the array
/// buffer reference in the array container or may escape it.
SILInstruction *NonAtomicRCTransformer::analyzeBB(SILValue ArrayContainer, SILInstruction *Start) {
  auto *BB = Start->getParent();
  auto II = Start->getIterator();
  while (II != BB->end()) {
    auto I = &*II++;
    // Check if instruction may overwrite the array buffer reference in the
    // container.
    if (auto *SI = dyn_cast<StoreInst>(I)) {
      // Check if this instruction may store into a memory location
      // aliasing the location where array buffer reference is stored.
      auto Dest = SI->getDest();
      if (isStoreAliasingArrayValue(ArrayContainer.getDef(), Dest)) {
        // Such an assignment is usually followed by a retain of the
        // new buffer and release of the old one. The release of the
        // old one could be done non-atomically.
        while (II != BB->end()) {
          auto *RI = &*II++;
          if (!isa<RefCountingInst>(RI))
            break;
          if (isa<StrongReleaseInst>(RI) || isa<ReleaseValueInst>(RI)) {
            if (isRCofArrayValueAt(ArrayContainer.getDef(), RI)) {
              cast<RefCountingInst>(RI)->setNonAtomic(true);
              llvm::dbgs() << "RC operation inside make_mutable region can be "
                              "non-atomic: ";
              RI->dump();
              break;
            }
          }
        }
        return I;
      }
      continue;
    }

    if (auto AI = FullApplySite::isa(I)) {
      ArraySemanticsCall ArrayCall(AI.getInstruction());
      if (ArrayCall && ArrayCall.getKind() == ArrayCallKind::kMakeMutable &&
          ArrayCall.getSelf() == ArrayContainer) {
        // This is a make_mutable call on the same array.
        // Therefore it can be simply eliminated.
        llvm::dbgs() << "make_mutable call can be eliminated:\n";
        (*ArrayCall).dumpInContext();
        ArrayCall.removeCall();
        // TODO: Rescan the release instruction?
        continue;
      }
      // Can this call escape the array container or array buffer reference?
      // TODO: Ask Erik how to query the EA in a proper way. We need to know
      // if the provided value can REALLY escape inside the function being called.
      // Specifically, even if it is passed as "inout" parameter.
      // If it can be overwritten in the function, then it essentially equivalent
      // to a store to the array and thus ends the region.
      // If it escapes inside the function, it also ends the region.
      // But what if it is only read inside the function? it would be nice if EA
      // would say it does not escape.
      // TODO: We want an API to check if a given SILValue is an argument of a
      // apply site and if it is escaping inside the function.
      if (EA->canEscapeTo(ArrayContainer, AI))
        return I;
      continue;
    }

    if (auto *RC = dyn_cast<RefCountingInst>(I)) {
      auto Ref = RC->getOperand(0);
      // If this is the array buffer reference or if this is
      // the array container itself, then it can be replaced
      // by a non-atomic variant.
      if (isRCofArrayValueAt(ArrayContainer.getDef(), I)) {
        RC->setNonAtomic(true);
        llvm::dbgs() << "RC operation inside make_mutable region can be "
                        "non-atomic: ";
        RC->dump();
      }
    }

    // Nothing else can change or escape the array buffer reference.
    continue;
  }

  return nullptr;
}

/// Compute a region where the buffer reference is non-escaping
/// and unique, i.e. it is thread-safe.
/// The region starts at a given apply instruction and ends
/// along each raeachable path as soon as there is an instruction
/// that may make the buffer non-unique (i.e. increase its RefCount)
/// or may write into the array and change the value of the buffer
/// reference. An apply site which can escape the buffer pointer
/// or may replace the buffer pointer is also such an example.
void NonAtomicRCTransformer::computeThreadSafeRegion(ArraySemanticsCall Call) {
  // Use forward dataflow analysis to compute the region.
  llvm::dbgs() << "Start of make_mutable region at:\n";
  (*Call).dumpInContext();

  SmallVector<SILBasicBlock *, 16> Worklist;
  auto *I = &*Call;
  Worklist.push_back(I->getParent());
  // TODO: It should be a forward propagation. All BBs dominated
  // by the Call's BB are potentially in the region.
  // Start with the Call's BB, the proceed with its successors,
  // and so on.
  auto Stop = analyzeBB(Call.getSelf(), &*++I->getIterator());
  if (Stop) {
    llvm::dbgs() << "End of make_mutable region at:\n";
    Stop->dumpInContext();
  }
  if (!Stop) {
    for (auto &S : I->getParent()->getSuccessors()) {
      Worklist.push_back(S);
    }
  }
}

/// Find all make_mutable calls and optimize
/// the regions of code starting at those calls.
/// Inside those regions, any RC operations
/// on the array can be non-atomic. Subsequent
/// make_mutable calls on the same array can
/// be eliminated.
/// FIXME: Currently, make_mutable calls are
/// processed one by one for each array. This
/// may result in multiple scans over a function.
void NonAtomicRCTransformer::findAllMakeUnique() {
  unsigned UniqueIdx = 0;
  for (SILBasicBlock &BB : *F) {
    SILInstruction *LastNonMatching = &*BB.begin();
    SILInstruction *LastMatching = nullptr;
    for (auto Iter = BB.begin(); Iter != BB.end();) {
      SILInstruction *I = &*Iter++;
      if (!isa<ApplyInst>(I) || I == LastMatching) {
        LastNonMatching = I;
        continue;
      }
      auto Call = isMakeUniqueCall(I);
      if (Call && Call.getSelf() &&
          checkUniqueArrayContainer(F, Call.getSelf())) {
        // Add to the set of makeUnique calls
        // The COW object that is made a thread-local by this call.
        auto CowObject = Call.getSelf();
        llvm::dbgs() << "\nThe following onbject is made thread-local: "
                     << CowObject << "\n";
        llvm::dbgs() << " by the instruction:\n";
        I->dumpInContext();

        // Create a region for this cow value.
        // If we have seen a region for the same value already, we should
        // assign the same index to it.
        unsigned Id = 0;
        if (CowValueId.count(CowObject))
          Id = CowValueId.lookup(CowObject);
        else {
          Id = UniqueIdx++;
          CowValueId[CowObject] = Id;
        }

        Regions.push_back(Region(I, CowObject, Id));
#if 0
        // Compute the non-escaping region, where the buffer pointer is known to
        // be non-escaping and thread-safe.
        computeThreadSafeRegion(Call);
        LastMatching = I;
        Iter = LastNonMatching->getIterator();
#endif
        continue;
      }
    }
  }
}

bool NonAtomicRCTransformer::process() {
  llvm::dbgs() << "About to process function:\n";
  F->dump();
  // Identify the beginning of all regions.
  findAllMakeUnique();
  // Perform a datafow analysis to find out the span
  // of each region.
  DF.compute(Regions);

  bool Changed = false;
  // Search the whole function for stack promotable allocations.
  for (SILBasicBlock &BB : *F) {
    for (auto Iter = BB.begin(); Iter != BB.end();) {
      // The allocation instruction may be moved, so increment Iter prior to
      // doing the optimization.
      SILInstruction *I = &*Iter++;
      if (isEligableRefCountingInst(I)) {
        Changed |= tryNonAtomicRC(I);
      }
    }
  }
  if (Changed) {
    F->dump();
  }
  return Changed;
}

} // end anonymous namespace

SILTransform *swift::createNonAtomicRC() { return new NonAtomicRC(); }
