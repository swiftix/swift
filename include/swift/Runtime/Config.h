//===--- Config.h - Swift Language Platform Configuration -------*- C++ -*-===//
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
// Definitions of common interest in Swift.
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_RUNTIME_CONFIG_H
#define SWIFT_RUNTIME_CONFIG_H

/// Does the current Swift platform support "unbridged" interoperation
/// with Objective-C?  If so, the implementations of various types must
/// implicitly handle Objective-C pointers.
///
/// Apple platforms support this by default.
#ifndef SWIFT_OBJC_INTEROP
#ifdef __APPLE__
#define SWIFT_OBJC_INTEROP 1
#else
#define SWIFT_OBJC_INTEROP 0
#endif
#endif

/// Does the current Swift platform allow information other than the
/// class pointer to be stored in the isa field?  If so, when deriving
/// the class pointer of an object, we must apply a
/// dynamically-determined mask to the value loaded from the first
/// field of the object.
///
/// According to the Objective-C ABI, this is true only for 64-bit
/// platforms.
#ifndef SWIFT_HAS_ISA_MASKING
#if SWIFT_OBJC_INTEROP && defined(__LP64__)
#define SWIFT_HAS_ISA_MASKING 1
#else
#define SWIFT_HAS_ISA_MASKING 0
#endif
#endif

// We try to avoid global constructors in the runtime as much as possible.
// These macros delimit allowed global ctors.
#if __clang__
# define SWIFT_ALLOWED_RUNTIME_GLOBAL_CTOR_BEGIN \
    _Pragma("clang diagnostic push") \
    _Pragma("clang diagnostic ignored \"-Wglobal-constructors\"")
# define SWIFT_ALLOWED_RUNTIME_GLOBAL_CTOR_END \
    _Pragma("clang diagnostic pop")
#else
# define SWIFT_ALLOWED_RUNTIME_GLOBAL_CTOR_BEGIN
# define SWIFT_ALLOWED_RUNTIME_GLOBAL_CTOR_END
#endif

// Bring in visibility attribute macros
#include "../../../stdlib/public/SwiftShims/Visibility.h"

// Define mappings for calling conventions.

#define CALLING_CONVENTION(CC) CALLING_CONVENTION_##CC

#define CALLING_CONVENTION_preserve_most __attribute__((preserve_most))
#define CALLING_CONVENTION_preserve_all  __attribute__((preserve_all))
#define CALLING_CONVENTION_c

// RUNTIME_CC0 is the standard C calling convention.
#define RUNTIME_CC0 c
#define CALLING_CONVENTION_RUNTIME_CC0 CALLING_CONVENTION_c
#define RUNTIME_CC0_IMPL c
#define CALLING_CONVENTION_RUNTIME_CC0_IMPL CALLING_CONVENTION_c

// RUNTIME_CC1 is a dedicated runtime calling convention to be used
// when calling the most popular runtime functions.
#if  defined(__arm64__) || defined(__x86_64__)
#define RUNTIME_CC1 preserve_most
#define CALLING_CONVENTION_RUNTIME_CC1 CALLING_CONVENTION_preserve_most
#define RUNTIME_CC1_IMPL preserve_most
#define CALLING_CONVENTION_RUNTIME_CC1_IMPL CALLING_CONVENTION_preserve_most
#else
#define RUNTIME_CC1 c
#define CALLING_CONVENTION_RUNTIME_CC1 CALLING_CONVENTION_c
#define RUNTIME_CC1_IMPL c
#define CALLING_CONVENTION_RUNTIME_CC1_IMPL CALLING_CONVENTION_c
#endif

#if defined(SWIFT_RUNTIME_PUBLIC_WRAPPERS)
// Make wrappers visible if they are build e.g. as a part of a shared libary for
// use in the -interpret mode.
#define SWIFT_RUNTIME_WRAPPER_VISIBILITY SWIFT_RUNTIME_EXPORT
#else
// Bring in visibility attribute macros for library visibility.
#include "llvm/Support/Compiler.h"
// Mark wrappers as hidden to avoid any conflicts.
#define SWIFT_RUNTIME_WRAPPER_VISIBILITY LLVM_LIBRARY_VISIBILITY
#endif

#endif // SWIFT_RUNTIME_CONFIG_H
