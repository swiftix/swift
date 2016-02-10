set(swift_static_client_runtime_compile_flags ${SWIFT_CORE_CXX_FLAGS})
list(APPEND swift_static_client_runtime_compile_flags "-ffunction-sections")
set(swift_static_client_runtime_link_flags)

# StaticClientRuntime is linked with any Swift executable or dylibs.
add_swift_library(swiftStaticClientRuntime IS_STDLIB IS_STDLIB_CORE
  StaticRuntimeWrappers.cpp
  LINK_FLAGS ${swift_static_client_runtime_link_flags}
  C_COMPILE_FLAGS ${swift_static_client_runtime_compile_flags}
  INSTALL_IN_COMPONENT stdlib)
