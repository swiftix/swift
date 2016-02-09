set(swift_client_runtime_compile_flags ${SWIFT_CORE_CXX_FLAGS})
set(swift_dyn_client_runtime_link_flags)
set(swift_dyn_client_runtime_compile_flags ${SWIFT_CORE_CXX_FLAGS})


list(APPEND swift_dyn_client_runtime_link_flags "-undefined" "dynamic_lookup")
list(APPEND swift_dyn_client_runtime_compile_flags "-DSWIFT_RUNTIME_PUBLIC_WRAPPERS")

add_swift_library(swiftClientRuntime IS_STDLIB IS_STDLIB_CORE
  RuntimeWrappers.cpp
  C_COMPILE_FLAGS ${swift_client_runtime_compile_flags}
  INSTALL_IN_COMPONENT stdlib)


add_swift_library(swiftDynClientRuntime SHARED IS_STDLIB IS_STDLIB_CORE
  RuntimeWrappers.cpp
  LINK_FLAGS ${swift_dyn_client_runtime_link_flags}
  C_COMPILE_FLAGS ${swift_dyn_client_runtime_compile_flags}
  INSTALL_IN_COMPONENT stdlib)

