set(swift_runtime_compile_flags ${SWIFT_CORE_CXX_FLAGS})

add_swift_library(swiftClientRuntime IS_STDLIB IS_STDLIB_CORE
  RuntimeWrappers.cpp
  INSTALL_IN_COMPONENT stdlib)

