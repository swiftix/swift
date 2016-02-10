set(swift_dynamic_client_runtime_compile_flags ${SWIFT_CORE_CXX_FLAGS})
set(swift_dynamic_client_runtime_link_flags)
list(APPEND swift_dynamic_client_runtime_link_flags "-undefined" "dynamic_lookup")

# DynamicClientRuntime is linked only when using the interpreter/JIT mode.
add_swift_library(swiftDynamicClientRuntime SHARED IS_STDLIB IS_STDLIB_CORE
  DynamicRuntimeWrappers.cpp
  LINK_FLAGS ${swift_dynamic_client_runtime_link_flags}
  C_COMPILE_FLAGS ${swift_dynamic_client_runtime_compile_flags}
  INSTALL_IN_COMPONENT stdlib)

