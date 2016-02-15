//===--- RuntimeWrappers.h - Wrappers for runtime entry points --*- C++ -*-===//
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
// Wrappers for runtime entry points that have to be called indirectly to avoid
// issues with dynamic linking.
//
//===----------------------------------------------------------------------===//

#ifndef __RUNTIME_WRAPPERS_H
#define __RUNTIME_WRAPPERS_H

#include "swift/Runtime/Enum.h"
#include "swift/Runtime/HeapObject.h"
#include "swift/Runtime/Metadata.h"

#if SWIFT_OBJC_INTEROP
#include <objc/objc.h>
#endif

//#define RUNTIME_WRAPPERS_BINDING_IN_CLIENT_LIB 1

using namespace swift;

typedef void (*RuntimeEntry)();

// Set of runtime entry pointers using the same
// calling convention. The last element should be
// NULL.
typedef RuntimeEntry RuntimeEntrySet[];

// Calling conventions used by the runtime.
enum SwiftRuntimeCallingConventions {
  RuntimeCC_C,
  RuntimeCC_PreserveMost,
  RuntimeCC_PreserveAll,
};

// Declarations of arrays containing references to entry points.

// Pointers to entry points. This array is indexed
// by SwiftRuntimeCallingConventions.
// LLDB may use this array to discover all entry points
// and their calling conventions.
extern "C" const RuntimeEntry *const_swift_runtime_wrappers[];

extern "C" RuntimeEntry _all_swift_runtime_wrappers_c[];

extern "C" RuntimeEntry _all_swift_runtime_wrappers_preserve_most[];

extern "C" RuntimeEntry _all_swift_runtime_wrappers_preserve_all[];

// Pointers to entry points. This array is indexed
// by SwiftRuntimeCallingConventions.
// Instruments and other tools may use it to intercept
// these runtime calls.
extern "C" RuntimeEntry *all_swift_runtime_wrappers[];

// Value at index i is the kind of runtime entry that
// is stored at the same index in _all_swift_runtime_wrappers_xxxx arrays.
// The lower 16 bits represent the kind of the runtime entry.
// The upper 16 bits represent the calling convention.
// Tools can query this array to figure out which point is stored at which
// index and which calling convention it uses.
extern "C" const uint32_t swift_rt_symbol_indices[];

#define CC_ATTR(CC) CC_ATTR_##CC
#define CC_IMPL_ATTR(CC) CC_ATTR(CC)

// Define specific attributes of each calling convention.
#define CC_ATTR_preserve_most __attribute__((preserve_most))
#define CC_ATTR_preserve_all __attribute__((preserve_all))
#define CC_ATTR_c

#if 0
// Map runtime calling convention ot a calling convention known to Clang.
#if defined(x86_64) || defined(ARM64)
#define RUNTIME_CC1 preserve_most
#else
#define RUNTIME_CC1 preserve_most
#endif
#endif

//#define RUNTIME_CC0 c

#define CC_ENCODING(CC) (CC_ENCODING_##CC << 16)

enum CC_Encoding {
  CC_ENCODING_c,
  CC_ENCODING_preserve_most,
  CC_ENCODING_preserve_all,
  // Add any new runtime calling convention before this line,
  // after all existing ones.
};

#define RT_ENTRY_IMPL(Name) Name
//#define RT_ENTRY_IMPL(Name) _##Name##_
#define RT_ENTRY(Name) Name

// Enumeration representing all runtime entries that are invoked via wrappers.
enum SwiftRTSymbols {
#define NAMESPACE(Namespace) Namespace::
#define ARGNAME(Name) Name
#define ARGNAMES(...) __VA_ARGS__
#define ARGS(...)     __VA_ARGS__
#define RETURNS(...)  __VA_ARGS__
#define SYMBOL_NAME(Name) RT_SWIFT_##Name
#define FUNCTION(Id, Namespace, Name, CC, ReturnTys, ArgTys, Args, Attrs) \
  SYMBOL_NAME(Name),
#define FUNCTION_WITH_IMPL(Id, Namespace, Name, ImplName, CC, ReturnTys, ArgTys, Args, Attrs) \
  FUNCTION(Id, Namespace, Name, CC, ReturnTys, ArgTys, Args, Attrs)
#include "swift/client-runtime/RuntimeFunctions.def"
};

namespace swift {
// Declare all implementations of runtime entries which have to be called via
// indirect calls.
// All those methods should not be in the swift namespace, because they are
// internal to the runtime library.
#define FUNCTION(Id, Namespace, Name, CC, ReturnTys, ArgTys, Args, Attrs) \
  extern "C" ReturnTys RT_ENTRY_IMPL(Name) (ArgTys) CC_IMPL_ATTR(CC##_IMPL);

#define FUNCTION_WITH_IMPL(Id, Namespace, Name, ImplName, CC, ReturnTys, ArgTys, Args, Attrs) \
  extern "C" ReturnTys ImplName (ArgTys) CC_IMPL_ATTR(CC##_IMPL);

#define NAMESPACE(Namespace) Namespace::
#define ARGNAME(Name) Name
#define ARGNAMES(...) __VA_ARGS__
#define ARGS(...)     __VA_ARGS__
#define RETURNS(...)  __VA_ARGS__
#include "RuntimeFunctions.def"
} // end of namespace swift

#endif
