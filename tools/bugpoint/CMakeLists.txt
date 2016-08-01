add_swift_executable(swift-bugpoint
  BugDriver.cpp
  CrashDebugger.cpp
  ExecutionDriver.cpp
  ExtractFunction.cpp
  FindBugs.cpp
  Miscompilation.cpp
  OptimizerDriver.cpp
  ToolRunner.cpp
  bugpoint.cpp
  LINK_LIBRARIES
    swiftFrontend
    swiftIRGen
    swiftSILGen
    swiftSILOptimizer

    #swiftFrontend
    #swiftBasic
    #swiftAST
    #swiftLLVMPasses
    #swiftSIL
    #swiftSILGen
    #swiftSILOptimizer
    #swiftIRGen

    # Clang dependencies.
    # FIXME: Clang should really export these in some reasonable manner.
    # clangCodeGen
    # clangAST
  COMPONENT_DEPENDS support)


#set(LLVM_LINK_COMPONENTS
#  Analysis
#  BitWriter
#  CodeGen
#  Core
#  IPO
#  IRReader
#  InstCombine
#  Instrumentation
#  Linker
#  ObjCARCOpts
#  ScalarOpts
#  Support
#  Target
#  TransformUtils
#  Vectorize
#  )

# Support plugins.
set(LLVM_NO_DEAD_STRIP 1)


swift_install_in_component(compiler
    TARGETS swift-bugpoint
    RUNTIME DESTINATION "bin")
