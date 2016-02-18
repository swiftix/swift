//===--- ARCEntryPointBuilder.h ---------------------------------*- C++ -*-===//
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

#ifndef SWIFT_LLVMPASSES_ARCENTRYPOINTBUILDER_H
#define SWIFT_LLVMPASSES_ARCENTRYPOINTBUILDER_H

#include "swift/Basic/NullablePtr.h"
#include "swift/Runtime/Config.h"
#include "swift/Runtime/RuntimeFnWrappersGen.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/APInt.h"

namespace swift {

namespace RuntimeConstants {
  const auto ReadNone = llvm::Attribute::ReadNone;
  const auto ReadOnly = llvm::Attribute::ReadOnly;
  const auto NoReturn = llvm::Attribute::NoReturn;
  const auto NoUnwind = llvm::Attribute::NoUnwind;
  const auto ZExt = llvm::Attribute::ZExt;
}

using namespace RuntimeConstants;

/// A class for building ARC entry points. It is a composition wrapper around an
/// IRBuilder and a constant Cache. It cannot be moved or copied. It is meant
/// to be created once and passed around by reference.
class ARCEntryPointBuilder {
  using IRBuilder = llvm::IRBuilder<>;
  using Constant = llvm::Constant;
  using Type = llvm::Type;
  using Function = llvm::Function;
  using Instruction = llvm::Instruction;
  using CallInst = llvm::CallInst;
  using Value = llvm::Value;
  using Module = llvm::Module;
  using AttributeSet = llvm::AttributeSet;
  using Attribute = llvm::Attribute;
  using APInt = llvm::APInt;
  
  // The builder which we are wrapping.
  IRBuilder B;

  // The constant cache.
  NullablePtr<Constant> Retain;
  NullablePtr<Constant> Release;
  NullablePtr<Constant> CheckUnowned;
  NullablePtr<Constant> RetainN;
  NullablePtr<Constant> ReleaseN;
  NullablePtr<Constant> UnknownRetainN;
  NullablePtr<Constant> UnknownReleaseN;
  NullablePtr<Constant> BridgeRetainN;
  NullablePtr<Constant> BridgeReleaseN;

  // The type cache.
  NullablePtr<Type> ObjectPtrTy;
  NullablePtr<Type> BridgeObjectPtrTy;

  llvm::CallingConv::ID RuntimeCC;
  llvm::CallingConv::ID RuntimeCC1;

public:
  ARCEntryPointBuilder(Function &F)
      : B(&*F.begin()), Retain(), ObjectPtrTy(),
        RuntimeCC(LLVM_CC(RuntimeCC)),
        RuntimeCC1(LLVM_CC(RuntimeCC1)) {
    //TODO: If the target does not support the new calling convention,
    //set RuntimeCC1 to use a standard C calling convention.
  }

  ~ARCEntryPointBuilder() = default;
  ARCEntryPointBuilder(ARCEntryPointBuilder &&) = delete;
  ARCEntryPointBuilder(const ARCEntryPointBuilder &) = delete;

  ARCEntryPointBuilder &operator=(const ARCEntryPointBuilder &) = delete;
  void operator=(ARCEntryPointBuilder &&C) = delete;

  void setInsertPoint(Instruction *I) {
    B.SetInsertPoint(I);
  }

  Value *createInsertValue(Value *V1, Value *V2, unsigned Idx) {
    return B.CreateInsertValue(V1, V2, Idx);
  }

  Value *createExtractValue(Value *V, unsigned Idx) {
    return B.CreateExtractValue(V, Idx);
  }

  Value *createIntToPtr(Value *V, Type *Ty) {
    return B.CreateIntToPtr(V, Ty);
  }

  CallInst *createRetain(Value *V) {
    // Cast just to make sure that we have the right type.
    V = B.CreatePointerCast(V, getObjectPtrTy());

    // Create the call.
    CallInst *CI = B.CreateCall(getRetain(), V);
    CI->setTailCall(true);
    return CI;
  }

  CallInst *createRelease(Value *V) {
    // Cast just to make sure that we have the right type.
    V = B.CreatePointerCast(V, getObjectPtrTy());

    // Create the call.
    CallInst *CI = B.CreateCall(getRelease(), V);
    CI->setTailCall(true);
    return CI;
  }

  
  CallInst *createCheckUnowned(Value *V) {
    // Cast just to make sure that we have the right type.
    V = B.CreatePointerCast(V, getObjectPtrTy());
    
    CallInst *CI = B.CreateCall(getCheckUnowned(), V);
    CI->setTailCall(true);
    return CI;
  }

  CallInst *createRetainN(Value *V, uint32_t n) {
    // Cast just to make sure that we have the right object type.
    V = B.CreatePointerCast(V, getObjectPtrTy());
    CallInst *CI = B.CreateCall(getRetainN(), {V, getIntConstant(n)});
    CI->setTailCall(true);
    return CI;
  }

  CallInst *createReleaseN(Value *V, uint32_t n) {
    // Cast just to make sure we have the right object type.
    V = B.CreatePointerCast(V, getObjectPtrTy());
    CallInst *CI = B.CreateCall(getReleaseN(), {V, getIntConstant(n)});
    CI->setTailCall(true);
    return CI;
  }

  CallInst *createUnknownRetainN(Value *V, uint32_t n) {
    // Cast just to make sure that we have the right object type.
    V = B.CreatePointerCast(V, getObjectPtrTy());
    CallInst *CI = B.CreateCall(getUnknownRetainN(), {V, getIntConstant(n)});
    CI->setTailCall(true);
    return CI;
  }

  CallInst *createUnknownReleaseN(Value *V, uint32_t n) {
    // Cast just to make sure we have the right object type.
    V = B.CreatePointerCast(V, getObjectPtrTy());
    CallInst *CI = B.CreateCall(getUnknownReleaseN(), {V, getIntConstant(n)});
    CI->setTailCall(true);
    return CI;
  }

  CallInst *createBridgeRetainN(Value *V, uint32_t n) {
    // Cast just to make sure we have the right object type.
    V = B.CreatePointerCast(V, getBridgeObjectPtrTy());
    CallInst *CI = B.CreateCall(getBridgeRetainN(), {V, getIntConstant(n)});
    CI->setTailCall(true);
    return CI;
  }

  CallInst *createBridgeReleaseN(Value *V, uint32_t n) {
    // Cast just to make sure we have the right object type.
    V = B.CreatePointerCast(V, getBridgeObjectPtrTy());
    CallInst *CI = B.CreateCall(getBridgeReleaseN(), {V, getIntConstant(n)});
    CI->setTailCall(true);
    return CI;
  }

private:
  Module &getModule() {
    return *B.GetInsertBlock()->getModule();
  }

  /// getRetain - Return a callable function for swift_retain.
  Constant *getRetain() {
    if (Retain)
      return Retain.get();
    auto *ObjectPtrTy = getObjectPtrTy();
    auto *VoidTy = Type::getVoidTy(getModule().getContext());

    llvm::Constant *cache = nullptr;
    Retain = getWrapperFn(getModule(),
                           cache,
                           "swift_retain",
                           RT_ENTRY_REF_AS_STR(swift_retain),
                           RuntimeCC1,
                           {VoidTy},
                           {ObjectPtrTy},
                           {NoUnwind});

    return Retain.get();
  }

  /// getRelease - Return a callable function for swift_release.
  Constant *getRelease() {
    if (Release)
      return Release.get();
    auto *ObjectPtrTy = getObjectPtrTy();
    auto *VoidTy = Type::getVoidTy(getModule().getContext());

    llvm::Constant *cache = nullptr;
    Release = getWrapperFn(getModule(),
                           cache,
                           "swift_release",
                           RT_ENTRY_REF_AS_STR(swift_release),
                           RuntimeCC1,
                           {VoidTy},
                           {ObjectPtrTy},
                           {NoUnwind});

    return Release.get();
  }

  Constant *getCheckUnowned() {
    if (CheckUnowned)
      return CheckUnowned.get();
    
    auto *ObjectPtrTy = getObjectPtrTy();
    auto &M = getModule();
    auto AttrList = AttributeSet::get(M.getContext(), 1, Attribute::NoCapture);
    AttrList = AttrList.addAttribute(
        M.getContext(), AttributeSet::FunctionIndex, Attribute::NoUnwind);
    CheckUnowned = M.getOrInsertFunction("swift_checkUnowned", AttrList,
                                          Type::getVoidTy(M.getContext()),
                                          ObjectPtrTy, nullptr);
    return CheckUnowned.get();
  }

  /// getRetainN - Return a callable function for swift_retain_n.
  Constant *getRetainN() {
    if (RetainN)
      return RetainN.get();
    auto *ObjectPtrTy = getObjectPtrTy();
    auto *Int32Ty = Type::getInt32Ty(getModule().getContext());
    auto *VoidTy = Type::getVoidTy(getModule().getContext());

    llvm::Constant *cache = nullptr;
    RetainN = getWrapperFn(getModule(),
                           cache,
                           "swift_retain_n",
                           RT_ENTRY_REF_AS_STR(swift_retain_n),
                           RuntimeCC1,
                           {VoidTy},
                           {ObjectPtrTy, Int32Ty},
                           {NoUnwind});

    return RetainN.get();
  }

  /// Return a callable function for swift_release_n.
  Constant *getReleaseN() {
    if (ReleaseN)
      return ReleaseN.get();
    auto *ObjectPtrTy = getObjectPtrTy();
    auto *Int32Ty = Type::getInt32Ty(getModule().getContext());
    auto *VoidTy = Type::getVoidTy(getModule().getContext());

    llvm::Constant *cache = nullptr;
    ReleaseN = getWrapperFn(getModule(),
                            cache,
                            "swift_release_n",
                            RT_ENTRY_REF_AS_STR(swift_release_n),
                            RuntimeCC1,
                            {VoidTy},
                            {ObjectPtrTy, Int32Ty},
                            {NoUnwind});

    return ReleaseN.get();
  }

  /// getUnknownRetainN - Return a callable function for swift_unknownRetain_n.
  Constant *getUnknownRetainN() {
    if (UnknownRetainN)
      return UnknownRetainN.get();
    auto *ObjectPtrTy = getObjectPtrTy();
    auto *Int32Ty = Type::getInt32Ty(getModule().getContext());
    auto *VoidTy = Type::getVoidTy(getModule().getContext());

    llvm::Constant *cache = nullptr;
    UnknownRetainN = getRuntimeFn(getModule(),
                                  cache,
                                  "swift_unknownRetain_n",
                                  RuntimeCC,
                                  {VoidTy},
                                  {ObjectPtrTy, Int32Ty},
                                  {NoUnwind});

    return UnknownRetainN.get();
  }

  /// Return a callable function for swift_unknownRelease_n.
  Constant *getUnknownReleaseN() {
    if (UnknownReleaseN)
      return UnknownReleaseN.get();
    auto *ObjectPtrTy = getObjectPtrTy();
    auto *Int32Ty = Type::getInt32Ty(getModule().getContext());
    auto *VoidTy = Type::getVoidTy(getModule().getContext());

    llvm::Constant *cache = nullptr;
    UnknownReleaseN = getRuntimeFn(getModule(),
                                   cache,
                                   "swift_unknownRelease_n",
                                   RuntimeCC,
                                   {VoidTy},
                                   {ObjectPtrTy, Int32Ty},
                                   {NoUnwind});

    return UnknownReleaseN.get();
  }

  /// Return a callable function for swift_bridgeRetain_n.
  Constant *getBridgeRetainN() {
    if (BridgeRetainN)
      return BridgeRetainN.get();
    auto *BridgeObjectPtrTy = getBridgeObjectPtrTy();
    auto *Int32Ty = Type::getInt32Ty(getModule().getContext());

    llvm::Constant *cache = nullptr;
    BridgeRetainN = getRuntimeFn(getModule(),
                                 cache,
                                 "swift_bridgeObjectRetain_n",
                                 RuntimeCC,
                                 {BridgeObjectPtrTy},
                                 {BridgeObjectPtrTy, Int32Ty},
                                 {NoUnwind});
    return BridgeRetainN.get();
  }

  /// Return a callable function for swift_bridgeRelease_n.
  Constant *getBridgeReleaseN() {
    if (BridgeReleaseN)
      return BridgeReleaseN.get();

    auto *BridgeObjectPtrTy = getBridgeObjectPtrTy();
    auto *Int32Ty = Type::getInt32Ty(getModule().getContext());
    auto *VoidTy = Type::getVoidTy(getModule().getContext());

    llvm::Constant *cache = nullptr;
    BridgeReleaseN = getRuntimeFn(getModule(),
                                  cache,
                                  "swift_bridgeObjectRelease_n",
                                  RuntimeCC,
                                  {VoidTy},
                                  {BridgeObjectPtrTy, Int32Ty},
                                  {NoUnwind});
    return BridgeReleaseN.get();
  }

  Type *getObjectPtrTy() {
    if (ObjectPtrTy)
      return ObjectPtrTy.get();
    auto &M = getModule();
    ObjectPtrTy = M.getTypeByName("swift.refcounted")->getPointerTo();
    assert(ObjectPtrTy && "Could not find the swift heap object type by name");
    return ObjectPtrTy.get();
  }

  Type *getBridgeObjectPtrTy() {
    if (BridgeObjectPtrTy)
      return BridgeObjectPtrTy.get();
    auto &M = getModule();
    BridgeObjectPtrTy = M.getTypeByName("swift.bridge")->getPointerTo();
    assert(BridgeObjectPtrTy && "Could not find the swift bridge object type by name");
    return BridgeObjectPtrTy.get();
  }

  Constant *getIntConstant(uint32_t constant) {
    auto &M = getModule();
    auto *Int32Ty = Type::getInt32Ty(M.getContext());
    return Constant::getIntegerValue(Int32Ty, APInt(32, constant));
  }
};

} // end swift namespace

#endif

