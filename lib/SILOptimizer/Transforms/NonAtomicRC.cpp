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

STATISTIC(NumNonAtomicRC, "Number of non-atomic RC operations");

llvm::cl::opt<bool> PerformNonAtomicOpts(
    "non-atomic-opts", llvm::cl::init(true),
    llvm::cl::desc("Enable non-atomic reference counting optimizations"));

using namespace swift;

namespace {

typedef SILAnalysis::InvalidationKind StateChanges;

class NonAtomicRCTransformer {
  SILPassManager *PM;
  SILFunction *F;
  EscapeAnalysis::ConnectionGraph *ConGraph;
  EscapeAnalysis *EA;
  RCIdentityFunctionInfo *RCIFI;
  CallerAnalysis *CA;

public:
  NonAtomicRCTransformer(SILPassManager *PM, SILFunction *F,
                         EscapeAnalysis::ConnectionGraph *ConGraph,
                         EscapeAnalysis *EA, RCIdentityFunctionInfo *RCIFI,
                         CallerAnalysis *CA)
      : PM(PM), F(F), ConGraph(ConGraph), EA(EA), RCIFI(RCIFI), CA(CA) {}

  StateChanges process();

private:
  StateChanges processNonEscapingRefCountingInsts();
  bool isEligableRefCountingInst(SILInstruction *I);
  StateChanges tryNonAtomicRC(SILInstruction *I);
  bool isThreadLocalObject(SILValue Obj);
  bool isThreadLocalFunctionArg(SILArgument *Arg,
                                SmallVectorImpl<SILValue> &WorkList);
};

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

static void markAsNonAtomic(RefCountingInst *I) {
  //SILValue Op = I->getOperand(0);
  I->setNonAtomic();
}

/// Is it a reference counting instruction that is eligable to
/// be promoted to a non-atomic version?
bool NonAtomicRCTransformer::isEligableRefCountingInst(SILInstruction *I) {
  return isa<RefCountingInst>(I) && !cast<RefCountingInst>(I)->isNonAtomic();
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

/// Check if the the parameter \V is based on a local object, e.g. it is an
/// allocation instruction or a struct/tuple constructed from the local objects.
/// Returns a found local object. If a local object was not found, returns an
/// empty SILValue.
static SILValue getLocalObject(SILValue V) {
  // It should be a local object.
  V = obtainUnderlyingObject(V);
  if (isa<AllocationInst>(V))
    return V;
  if (isa<LiteralInst>(V))
    return V;
  // Look through strong_pin instructions.
  if (auto *SPI = dyn_cast<StrongPinInst>(V))
    return getLocalObject(SPI->getOperand());
  if (auto *SI = dyn_cast<StructInst>(V)) {
    for (auto &Op : SI->getAllOperands())
      if (!getLocalObject(Op.get()))
        return SILValue();
    return V;
  }
  if (auto *TI = dyn_cast<TupleInst>(V)) {
    for (auto &Op : TI->getAllOperands())
      if (!getLocalObject(Op.get()))
        return SILValue();
    return V;
  }

  if (auto Arg = dyn_cast<SILArgument>(V)) {
    DEBUG(llvm::dbgs() << "Analyze incoming values for " << *Arg << "\n");
    // It is local, if its input values are local on all paths.
    SmallVector<SILValue, 4> IncomingValues;
    if (Arg->getIncomingValues(IncomingValues)) {
      llvm::SmallSetVector<SILValue, 4> Results;
      for (auto InValue : IncomingValues) {
        auto LocalObject = getLocalObject(InValue);
        if (!LocalObject) {
          DEBUG(llvm::dbgs() << "Analyzed incoming value: " << InValue << " ->  unknown\n");
          return SILValue();
        }
        DEBUG(llvm::dbgs() << "Analyzed incoming value: " << InValue << " -> "
                           << LocalObject << "\n");
        Results.insert(LocalObject);
      }
      DEBUG(llvm::dbgs() << "All incoming values are local for: " << *Arg
                         << ". There are " << Results.size()
                         << " different incoming values\n");
      if (Results.size() == 1) {
        return Results.pop_back_val();
      }
      return SILValue();
    } else {
      DEBUG(llvm::dbgs() << "Could not determine incoming values for " << *Arg << "\n");
    }
  }

  return SILValue();
}

/// Check if a given value escapes inside the function it belongs to.
static bool isEscapingObject(SILValue V,
                             EscapeAnalysis *EA,
                             bool ArgNotEscapes = false) {
  auto F = V->getParentBB()->getParent();
  auto *ConGraph = EA->getConnectionGraph(F);
  auto *Node = ConGraph->getNodeOrNull(V, EA);

  if (!Node) {
    DEBUG(llvm::dbgs() << "No node in the conn graph for the local object: "; V->dump());
    return true;
  }

  // As long as the value does not escape the function, it is fine.
  if (Node->escapesInsideFunction(
          //isNotAliasingArgument(V, InoutAliasingAssumption::NotAliasing))) {
          ArgNotEscapes)) {
    DEBUG(llvm::dbgs() << "Conn graph node escapes for the local object: ";
          V->dump());
    return true;
  }

  // The value does not escape.
  return false;
}

/// Return the single return value of the function.
static SILValue findReturnValue(SILFunction *F) {
  auto RBB = F->findReturnBB();
  if (RBB == F->end())
    return SILValue();
  auto Term = dyn_cast<ReturnInst>(RBB->getTerminator());
  return Term->getOperand();
}

/// Check if a function argument is a thread-local object.
bool NonAtomicRCTransformer::isThreadLocalFunctionArg(
    SILArgument *Arg, SmallVectorImpl<SILValue> &WorkList) {
  assert(Arg->isFunctionArg() && "Function argument expected");
  // Check if the this function argument is a thread local object at all
  // call sites. In this case we can treat this function argument as
  // local object.
  auto &CallerInfo = CA->getCallerInfo(Arg->getFunction());
  if (CallerInfo.isIncomplteCallerSet())
    return false;
  // Bail on partial applies.
  if (CallerInfo.getMinPartialAppliedArgs())
    return false;
  llvm::dbgs() << "Found argument of a function whose callers set is known: "
               << Arg->getParentBB()->getParent()->getName() << ":\n"
               << "Arg description: ";
  Arg->dump();
  if (isEscapingObject(Arg, EA, /*ArgNotEscapes*/ true))
    return false;
  // We know all callers of the current function.
  auto &CallerSites = CallerInfo.getCallerSites();
  auto ArgIdx = Arg->getIndex();
  for (auto Pair : CallerSites) {
    auto &CurCallerSites = Pair.second;
    for (auto CallerSite : CurCallerSites) {
      // Analyze the argument passed for the Arg at the
      // given current call site.
      if (auto FAS = FullApplySite::isa(CallerSite)) {
        // Bail if it is a partial apply and we don't
        // have enough arguments.
        if (ArgIdx >= FAS.getNumArguments())
          return false;
        auto PassedArg = FAS.getArgument(ArgIdx);
        WorkList.push_back(PassedArg);
        llvm::dbgs() << "Analyze passed argument of "
                     << Arg->getParentBB()->getParent()->getName() << ":\n"
                     << "Arg description: ";
        Arg->dump();
        llvm::dbgs() << "Passed arg value: ";
        PassedArg->dump();
        continue;
      }
      // We don't know what it is.
      return false;
    }
  }
  return true;
}

bool NonAtomicRCTransformer::isThreadLocalObject(SILValue Obj) {
  // Set of values to be checked for their locality.
  SmallVector<SILValue, 8> WorkList;
  // Set of processed values.
  llvm::SmallPtrSet<SILValue, 8> Processed;
  WorkList.push_back(Obj);

  while (!WorkList.empty()) {
    auto V = WorkList.pop_back_val();
    if (!V)
      return false;
    if (Processed.count(V))
      continue;
    Processed.insert(V);
    // It should be a local object.
    //V = getUnderlyingObject(V);
    V = obtainUnderlyingObject(V);
    if (auto I = dyn_cast<SILInstruction>(V)) {
      if (isa<AllocationInst>(V)) {
        if (isEscapingObject(V, EA))
          return false;
        continue;
      }
      if (isa<StrongPinInst>(I)) {
        WorkList.push_back(I->getOperand(0));
        continue;
      }
      if (isa<StructInst>(I) || isa<TupleInst>(I) || isa<EnumInst>(I)) {
        // A compound value is local, if all of its components are local.
        for (auto &Op : I->getAllOperands()) {
          WorkList.push_back(Op.get());
        }
        continue;
      }
      if (isa<TupleExtractInst>(I) || isa<StructExtractInst>(I) ||
          isa<UncheckedEnumDataInst>(I)) {
        // The result of tuple_extract/struct_extract is thread-local if its
        // operand is thread local.
        WorkList.push_back(I->getOperand(0));
        continue;
      }
      if (isa<RawPointerToRefInst>(V) || isa<AddressToPointerInst>(V)) {
        WorkList.push_back(I->getOperand(0));
        continue;
      }
      if (FullApplySite AS = FullApplySite::isa(I)) {
        // Check if result of call was a local object in the callee.
        auto Callee = AS.getCalleeFunction();

        DEBUG(if (Callee) llvm::dbgs()
              << "Check the result of the function call: " << Callee->getName()
              << "\n");

        // Can we analyze the body of the function?
        if (!Callee)
          return false;

        if (Callee->isExternalDeclaration()) {
          // A special handling for some stdlib functions.
          if (Callee->getName().find("TFSaap9subscriptFSix", 0) !=
              StringRef::npos) {
            // This is a Array.subscript.nativePinningMutableAddressor call.
            // The result is always unique and thus thread-local.
            continue;
          }
          return false;
        }

        // Find the return object.
        auto ReturnVal = findReturnValue(Callee);

        // Bail if there is no return value. This can happen if the callee
        // ends with an unreachable instruction.
        if (!ReturnVal)
          return false;

        // ???? Do we need this check???
        //if (isEscapingObject(ReturnVal, EA))
        //  return false;

        DEBUG(llvm::dbgs() << "Return value is not escaping for function: "
                           << Callee->getName() << "\n");
        // Check that ReturnVal is local to the function where it is defined.
        WorkList.push_back(ReturnVal);
        continue;
      }
    }

    if (auto Arg = dyn_cast<SILArgument>(V)) {
      // A BB argument is local if all of its
      // incoming values are local.
      if (Arg->isFunctionArg()) {
        if (!isThreadLocalFunctionArg(Arg, WorkList))
          return false;
        continue;
      }

      // Process a BB argument.
      SmallVector<SILValue, 4> IncomingValues;
      if (Arg->getIncomingValues(IncomingValues)) {
        for (auto InValue : IncomingValues) {
          WorkList.push_back(InValue);
        }
        continue;
      }
    }

    // Everything else is considered to be non-local.
    if (!isa<LoadInst>(V)) {
      llvm::dbgs() << "Unknown RC value: ";
      V->dump();
    }
    return false;
  }
  return true;
}

/// Try to promote a reference counting instruction to its non-atomic
/// variant.
StateChanges NonAtomicRCTransformer::tryNonAtomicRC(SILInstruction *I) {
  assert(isa<RefCountingInst>(I));
  auto *RCInst = cast<RefCountingInst>(I);

  // For the EscapeAnalysis to be correct, it should be a local object.
  auto LocalObject = RCInst->getOperand(0);
  auto IsLocalObject = isThreadLocalObject(LocalObject);
  //auto LocalObject = RCInst->getOperand(0);
  if (!IsLocalObject) {
    DEBUG(llvm::dbgs() << "Operand of instruction is not local: "; LocalObject->dump());
    return SILAnalysis::InvalidationKind::Nothing;
  }

  // This value does not escape, which means that it is
  // thread-local.
  // Use non-atomic RC instructions for it.
  markAsNonAtomic(RCInst);
  NumNonAtomicRC++;
  DEBUG(llvm::dbgs() << "Marking the RC instruction as non-atomic:\n";
        RCInst->dumpInContext(););
  return SILAnalysis::InvalidationKind::Instructions;
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
        DEBUG(llvm::dbgs() << "Consider eligable instruction: "; I->dump());
        Changes = StateChanges(Changes | tryNonAtomicRC(I));
      }
    }
  }
  return Changes;
}

StateChanges NonAtomicRCTransformer::process() {
  DEBUG(llvm::dbgs() << "\nAbout to process function:\n"; F->dump());
  auto ChangesRefCounting = processNonEscapingRefCountingInsts();

  if (ChangesRefCounting) {
    DEBUG(llvm::dbgs() << "\n\nFunction after the transformation:"; F->dump());
  }

  return StateChanges(ChangesRefCounting);
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

    DEBUG(llvm::dbgs() << "** Start NonAtomicRC for " << getFunction()->getName()
                       << " **\n");

    auto *EA = PM->getAnalysis<EscapeAnalysis>();
    auto *RCIA = PM->getAnalysis<RCIdentityAnalysis>();
    auto *CA = PM->getAnalysis<CallerAnalysis>();

    SILFunction *F = getFunction();
    auto *ConGraph = EA->getConnectionGraph(F);
    if (ConGraph) {
      DEBUG(ConGraph->dump());
      NonAtomicRCTransformer Transformer(PM, F, ConGraph, EA, RCIA->get(F), CA);
      auto Changes = Transformer.process();
      if (Changes) {
        PM->invalidateAnalysis(F, Changes);
      }
    }
    DEBUG(llvm::dbgs() << "** End NonAtomicRC for " << getFunction()->getName()
                       << " **\n");

  }

  StringRef getName() override { return "NonAtomicRC"; }
};

} // end anonymous namespace

SILTransform *swift::createNonAtomicRC() { return new NonAtomicRC(); }
