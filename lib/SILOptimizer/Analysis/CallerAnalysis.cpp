//===--- CallerAnalysis.cpp - Determine callsites to a function  ----------===//
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

#include "swift/SILOptimizer/Analysis/CallerAnalysis.h"

#include "swift/Basic/Fallthrough.h"
#include "swift/SIL/SILModule.h"
#include "swift/SILOptimizer/Utils/Local.h"
#include "swift/SIL/DebugUtils.h"

using namespace swift;

void CallerAnalysis::processFunctionCallSites(SILFunction *F) {
  // Scan the whole module and search Apply sites.
  FunctionInfo &CallerInfo = FuncInfos[F];
  CallerInfo.setFunction(F);
  for (auto &BB : *F) {
    for (auto &II : BB) {
#if 1
      auto FRI = dyn_cast<FunctionRefInst>(&II);
      if (!FRI)
        continue;
      auto CalleeFn = FRI->getReferencedFunction();
      if (!CalleeFn)
        continue;

      FunctionInfo &CalleeInfo = FuncInfos[CalleeFn];
      bool IsReference = false;

      SmallVector<SILValue, 8> WorkList;
      WorkList.push_back(FRI);

      // Analyze how this function reference is used.
      // Do a recusrive walk over all its uses to figure
      // this out.
      while (!WorkList.empty()) {
        auto V = WorkList.pop_back_val();
        // Analyze how this function reference is used.
        for (auto Use : getNonDebugUses(V)) {
          auto User = Use->getUser();
          if (FullApplySite::isa(User)) {
            // Update the callee information for this function.
            CallerInfo.Callees.insert(CalleeFn);

            // Update the callsite information for the callee.
            if (!CalleeInfo.Callers.count(F))
              CalleeInfo.Callers[F] = false;
            CalleeInfo.CallerSites[F].push_back(User);
            continue;
          }

          if (auto PAI = dyn_cast<PartialApplyInst>(User)) {
            // Update the callee information for this function.
            CallerInfo.Callees.insert(CalleeFn);

            // Update the partial-apply information for the callee.
            int &minAppliedArgs = CalleeInfo.PartialAppliers[F];
            int numArgs = (int)PAI->getNumArguments();
            if (minAppliedArgs == 0 || numArgs < minAppliedArgs) {
              minAppliedArgs = numArgs;
            }
            // partiall apply itself is not considered a call.
            for (auto Use : getNonDebugUses(User)) {
              WorkList.push_back(Use->get());
            }
            continue;
          }

          if (isa<ThinToThickFunctionInst>(User) || isa<ConvertFunctionInst>(User)) {
            for (auto Use : getNonDebugUses(User)) {
              WorkList.push_back(Use->get());
            }
            continue;
          }

          // This is not an apply or partial apply of a casted
          // function reference. Consider it as a pointer.
          IsReference = true;
        }
      }

      if (IsReference) {
        // Register the fact that a reference was taken.
        CallerInfo.Callees.insert(CalleeFn);
        CalleeInfo.setReferencedByCaller(F);
      }
#endif
#if 0
      if (auto Apply = FullApplySite::isa(&II)) {
        SILFunction *CalleeFn = Apply.getCalleeFunction();
        if (!CalleeFn)
          continue;

        // Update the callee information for this function.
        FunctionInfo &CallerInfo = FuncInfos[F];
        CallerInfo.Callees.insert(CalleeFn);

        // Update the callsite information for the callee.
        FunctionInfo &CalleeInfo = FuncInfos[CalleeFn];
        CalleeInfo.Callers.insert(F);
        continue;
      }
      if (auto *PAI = dyn_cast<PartialApplyInst>(&II)) {
        SILFunction *CalleeFn = PAI->getCalleeFunction();
        if (!CalleeFn)
          continue;

        // Update the callee information for this function.
        FunctionInfo &CallerInfo = FuncInfos[F];
        CallerInfo.Callees.insert(CalleeFn);

        // Update the partial-apply information for the callee.
        FunctionInfo &CalleeInfo = FuncInfos[CalleeFn];
        int &minAppliedArgs = CalleeInfo.PartialAppliers[F];
        int numArgs = (int)PAI->getNumArguments();
        if (minAppliedArgs == 0 || numArgs < minAppliedArgs) {
          minAppliedArgs = numArgs;
        }
        continue;
      }
#endif
    }
  }
}

void CallerAnalysis::invalidateExistingCalleeRelation(SILFunction *F) {
  FunctionInfo &CallerInfo = FuncInfos[F];
  for (auto Callee : CallerInfo.Callees) {
    FunctionInfo &CalleeInfo = FuncInfos[Callee];
    CalleeInfo.setNotReferencedByCaller(F);
    CalleeInfo.Callers.erase(F);
    CalleeInfo.PartialAppliers.erase(F);
    CalleeInfo.CallerSites.erase(F);
  }
}

//===----------------------------------------------------------------------===//
//                              Main Entry Point
//===----------------------------------------------------------------------===//
SILAnalysis *swift::createCallerAnalysis(SILModule *M) {
  return new CallerAnalysis(M);
}
