// Produce globals referencing runtime entry symbols only for entries that 
// demand it.
//
// Each runtime function definition in RuntimeFunctions.def should
// indicate if it requires a global referencing it.
//
// All entries using the RuntimeCC1 calling convention need a global, because
// they are always invoked indirectly.
//
// Runtime entries using the RuntimeCC calling convention do not demand a global
// by default. They can optionally ask for it.

#include "swift/Runtime/HeapObject.h"
#include "swift/Runtime/Metadata.h"
#include "swift/Runtime/Enum.h"

#define FOR_CONV_RuntimeCC(...)
#define FOR_CONV_C_CC(...)
#define FOR_CONV_RuntimeCC1(x) x

typedef void (*RuntimeEntry)();

#define DEFINE_SYMBOL(SymbolName, Name) \
  SWIFT_RUNTIME_EXPORT extern "C" RuntimeEntry SymbolName = reinterpret_cast<RuntimeEntry>(Name);

#define RT_ENTRY_SYMBOL_NAME(Name) _##Name
// TODO: Use _##Name##_ instead?
#define RT_ENTRY_IMPL(Name) Name

#define FUNCTION1(Id, Name, CC, ReturnTys, ArgTys, Attrs)                      \
  DEFINE_SYMBOL(RT_ENTRY_SYMBOL_NAME(Name), Name)

// Automatically generate a global symbol name if it is required by the calling
// convention.
#define FUNCTION(Id, Name, CC, ReturnTys, ArgTys, Attrs)                       \
  FOR_CONV_##CC(FUNCTION1(Id, Name, CC, ReturnTys, ArgTys, Attrs))

// Allow for custom global symbol name.
#define FUNCTION_WITH_GLOBAL_SYMBOL(Id, Name, GlobalSymbolName, CC, ReturnTys, \
                                    ArgTys, Attrs)                             \
  DEFINE_SYMBOL(GlobalSymbolName, Name)

// FIXME: Put it into a header
extern "C" Class swift_getInitializedObjCClass(Class c)
    CALLING_CONVENTION(RUNTIME_CC1);


namespace swift {
#include "swift/../../lib/IRGen/RuntimeFunctions.def"
}

