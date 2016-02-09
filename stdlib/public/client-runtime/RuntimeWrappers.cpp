#include "swift/client-runtime/RuntimeWrappers.h"

#if defined(RUNTIME_WRAPPERS_BINDING_IN_CLIENT_LIB)
// Initialization of runtime wrappers bindings.

static const RuntimeEntry _const_swift_runtime_wrappers_c[]  = {
  nullptr,
};

static const RuntimeEntry _const_swift_runtime_wrappers_preserve_most[]  = {
  nullptr,
};

static const RuntimeEntry _const_swift_runtime_wrappers_preserve_all[]  = {
  nullptr,
};

// Pointers to entry points. This array is indexed
// by SwiftRuntimeCallingConventions.
// LLDB may use this array to discover all entry points
// and their calling conventions.
extern "C" const RuntimeEntry *const_swift_runtime_wrappers[] = {
  _const_swift_runtime_wrappers_c,
  _const_swift_runtime_wrappers_preserve_most,
  _const_swift_runtime_wrappers_preserve_all
};

#define FUNCTION(Id, Namespace, Name, CC, ReturnTys, ArgTys, Args, Attrs) \
  (RuntimeEntry) RUNTIME_ENTRY_IMPL(Name),

extern "C" RuntimeEntry _all_swift_runtime_wrappers_c[]  = {
#include "swift/client-runtime/RuntimeFunctions.def"
  nullptr,
};

#define FUNCTION(Id, Namespace, Name, CC, ReturnTys, ArgTys, Args, Attrs) \
  (RuntimeEntry) RUNTIME_ENTRY_IMPL(Name),

extern "C" RuntimeEntry _all_swift_runtime_wrappers_preserve_most[] = {
#include "swift/client-runtime/RuntimeFunctions.def"
  nullptr,
};

#define FUNCTION(Id, Namespace, Name, CC, ReturnTys, ArgTys, Args, Attrs) \
  reinterpret_cast<RuntimeEntry>(RUNTIME_ENTRY_IMPL(Name)),

extern "C" RuntimeEntry _all_swift_runtime_wrappers_preserve_all[] = {
#include "swift/client-runtime/RuntimeFunctions.def"
  nullptr,
};


// Pointers to entry points. This array is indexed
// by SwiftRuntimeCallingConventions.
// Instruments and other tools may use it to intercept
// these runtime calls.
extern "C" RuntimeEntry *all_swift_runtime_wrappers[] = {
  _all_swift_runtime_wrappers_c,
  _all_swift_runtime_wrappers_preserve_most,
  _all_swift_runtime_wrappers_preserve_all
};

/// Entry point wrappers. They are called from the
/// compiled Swift code.

#define INVOKE_RT(CC, Entry, Proto) \
  ((Proto)(_all_swift_runtime_wrappers_##CC[Entry]))

#define SYMBOL_NAME(Name) RT_SWIFT_##Name

#define NAMESPACE(Namespace) Namespace::
#define ARGNAME(Name) Name
#define ARGNAMES(...) __VA_ARGS__
#define ARGS(...)     __VA_ARGS__
#define RETURNS(...)  __VA_ARGS__


#define FUNCTION(Id, Namespace, Name, CC, ReturnTys, ArgTys, Args, Attrs) \
  SYMBOL_NAME(Name) | CC_ENCODING(CC),


// Value at index i is the kind of runtime entry that
// is stored at the same index in _all_swift_runtime_wrappers_xxxx arrays.
// The lower 16 bits represent the kind of the runtime entry.
// The upper 16 bits represent the calling convention.
// Tools can query this array to figure out which point is stored at which
// index and which calling convention it uses.
extern "C" const uint32_t swift_rt_symbol_indices[] = {
#include "swift/client-runtime/RuntimeFunctions.def"
};

#endif

// TODO: Use a local pointer to cache the external address?
static RuntimeEntry * _local_all_swift_runtime_wrappers_c =
    _all_swift_runtime_wrappers_c;

#define INVOKE_RT(CC, Entry, Proto)                                            \
  (reinterpret_cast<Proto>(_all_swift_runtime_wrappers_##CC[Entry]))

#define SYMBOL_NAME(Name) RT_SWIFT_##Name
#define ATTR(Attr) __attribute__((Attr))

#define FUNCTION(Id, Namespace, Name, CC, ReturnTys, ArgTys, Args, Attrs)      \
  extern "C" SWIFT_RUNTIME_WRAPPER_VISIBILITY ReturnTys Namespace Name(ArgTys)          \
      CC_ATTR(CC) {                                                            \
    return INVOKE_RT(CC, SYMBOL_NAME(Name),                                    \
                     CC_IMPL_ATTR(CC##_IMPL) ReturnTys (*)(ArgTys))(Args);     \
  }

#define NAMESPACE(Namespace) Namespace::
#define ARGNAME(Name)        Name
#define ARGNAMES(...)        __VA_ARGS__
#define ARGS(...)            __VA_ARGS__
#define RETURNS(...)         __VA_ARGS__


// Generate wrappers for all runtime methods that have to be invoked indirectly.
#include "swift/client-runtime/RuntimeFunctions.def"
