//===--- AssumeSingleThreaded.cpp - Assume single-threaded executution  ---===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2016 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
// Assume that user code is single-thread 
//
// Convert all reference counting operations into non-atomic ones.
//
//===----------------------------------------------------------------------===//

#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SIL/SILFunction.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SIL/SILModule.h"
#include "swift/SILOptimizer/Utils/Local.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "llvm/Support/CommandLine.h"

using namespace swift;

llvm::cl::opt<bool> AssumeSingleThreadedFlag(
    "assume-single-threaded", llvm::cl::init(false),
    llvm::cl::Hidden,
    llvm::cl::desc(
        "Assume that code will be executed in a single-threaded environment"));

namespace {
class AssumeSingleThreaded : public swift::SILFunctionTransform {
  /// The entry point to the transformation.
  void run() override {
    if (!AssumeSingleThreadedFlag)
      return;
    for (auto &BB : *getFunction()) {
      for (auto &I : BB) {
        if (auto RCInst = dyn_cast<RefCountingInst>(&I))
          RCInst->setNonAtomic();
      }
    }
    invalidateAnalysis(SILAnalysis::InvalidationKind::Instructions);
  }

  StringRef getName() override { return "Assume single threaded"; }
};
} // end anonymous namespace


SILTransform *swift::createAssumeSingleThreaded() {
  return new AssumeSingleThreaded();
}
