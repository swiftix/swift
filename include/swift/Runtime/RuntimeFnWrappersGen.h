//===-- RuntimeFnWrapperGen.h - LLVM IR Generation for runtime functions --===//
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
//
//  Helper functions providing the LLVM IR generation for runtime entry points.
//
//===----------------------------------------------------------------------===//
#ifndef SWIFT_RUNTIME_RUNTIMEFNWRAPPERSGEN_H
#define SWIFT_RUNTIME_RUNTIMEFNWRAPPERSGEN_H

#include "llvm/IR/Module.h"
#include "llvm/ADT/ArrayRef.h"

namespace swift {

/// Generate an llvm declaration for a runtime entry with a
/// given name, return types, argument types, attributes and
/// a calling convention.
llvm::Constant *getRuntimeFn(llvm::Module &Module,
                      llvm::Constant *&cache,
                      char const *name,
                      llvm::CallingConv::ID cc,
                      std::initializer_list<llvm::Type*> retTypes,
                      std::initializer_list<llvm::Type*> argTypes,
                      llvm::ArrayRef<llvm::Attribute::AttrKind> attrs);

/// Generate an llvm wrapper for a runtime entry with a
/// given name, return types, argument types, attributes and a
/// calling convention.
/// Symbol is the name of a global symbol containing the
/// address of the runtime entry implementation.
/// The wrapper simply invokes a corresponding entry point
/// by means of an indirect call of the function currently
/// referenced by the symbol.
///
/// If the calling convention and the current target require a wrapper,
/// it will be generated. Each wrapper has a hidden linkage and marked
/// as ODR, so that a linker can merge all wrappers with the same
/// name into one wrapper.
///
/// If it the calling convention does not require a wrapper on the
/// current target, then this no wrapper will be generated and the result
/// is equivalent to the call of getRuntimeFn.
llvm::Constant *getWrapperFn(llvm::Module &Module, llvm::Constant *&cache,
                             char const *name, char const *symbol,
                             llvm::CallingConv::ID cc,
                             std::initializer_list<llvm::Type *> retTypes,
                             std::initializer_list<llvm::Type *> argTypes,
                             llvm::ArrayRef<llvm::Attribute::AttrKind> attrs);
} /* Namespace swift */
#endif
