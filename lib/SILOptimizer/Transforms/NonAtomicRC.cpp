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
#include "swift/SILOptimizer/Analysis/EscapeAnalysis.h"
#include "swift/SILOptimizer/Analysis/DominanceAnalysis.h"
#include "swift/SIL/SILArgument.h"
#include "swift/SIL/SILBuilder.h"
#include "llvm/ADT/Statistic.h"

STATISTIC(NumNonAtomicRC, "Number of non-atomic RC operations");

using namespace swift;

//===----------------------------------------------------------------------===//
//                              Top Level Driver
//===----------------------------------------------------------------------===//

namespace {

class NonAtomicRC : public SILFunctionTransform {
  EscapeAnalysis::ConnectionGraph *ConGraph;
  EscapeAnalysis *EA;

public:
  NonAtomicRC() {}

private:
  bool isEligableRefCountingInst(SILInstruction *I);
  bool process(SILFunction *F);
  bool tryNonAtomicRC(SILInstruction *I);

  /// The entry point to the transformation.
  void run() override {
    DEBUG(llvm::dbgs() << "** NonAtomicRC **\n");

    EA = PM->getAnalysis<EscapeAnalysis>();

    SILFunction *F = getFunction();
    ConGraph = EA->getConnectionGraph(F);
    if (ConGraph) {
      process(F);
    }
  }

  StringRef getName() override { return "NonAtomicRC"; }
};

bool NonAtomicRC::isEligableRefCountingInst(SILInstruction *I) {
  return isa<RefCountingInst>(I) && !cast<RefCountingInst>(I)->isNonAtomic();
}

bool NonAtomicRC::tryNonAtomicRC(SILInstruction *I) {
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


/// Compute a region where the buffer reference is non-escaping
/// and unique, i.e. it is thread-safe.
/// The region starts at a given apply instruction and ends
/// along each raeachable path as soon as there is an instruction
/// that may make the buffer non-unique (i.e. increase its RefCount)
/// or may write into the array and change the value of the buffer
/// reference. An apply site which can escape the buffer pointer
/// or may replace the buffer pointer is also such an example.
static void computeThreadSafeRegion(FullApplySite AI) {

}

static void findAllMakeUnique(SILFunction *F) {
  for (SILBasicBlock &BB : *F) {
    for (auto Iter = BB.begin(); Iter != BB.end();) {
      SILInstruction *I = &*Iter++;
      if (!isa<ApplyInst>(I))
        continue;
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
        // Compute the non-escaping region, where the buffer pointer is known to
        // be non-escaping and thread-safe.
        computeThreadSafeRegion(FullApplySite(I));
      }
    }
  }
}

bool NonAtomicRC::process(SILFunction *F) {
  llvm::dbgs() << "About to process function:\n";
  F->dump();
  findAllMakeUnique(F);
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
