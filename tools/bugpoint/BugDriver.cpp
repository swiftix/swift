//===- BugDriver.cpp - Top-Level BugPoint class implementation ------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This class contains all of the shared state and information that is used by
// the BugPoint tool to track down errors in optimizations.  This class is the
// main driver class that invokes all sub-functionality.
//
//===----------------------------------------------------------------------===//

#include "BugDriver.h"
#include "ToolRunner.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileUtilities.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include "swift/Subsystems.h"
#include "swift/AST/DiagnosticsFrontend.h"
#include "swift/Basic/SourceLoc.h"
#include "swift/Frontend/DiagnosticVerifier.h"
#include "swift/Frontend/Frontend.h"
#include "swift/Frontend/FrontendOptions.h"
#include "swift/Frontend/PrintingDiagnosticConsumer.h"
#include "swift/Serialization/SerializedSILLoader.h"
#include "swift/Serialization/SerializationOptions.h"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/SILOptimizer/PassManager/PassManager.h"
#include "swift/SIL/SILModule.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SIL/SILBasicBlock.h"
#include "swift/Strings.h"
#include <memory>
using namespace llvm;

namespace llvm {
  Triple TargetTriple;
}

// Anonymous namespace to define command line options for debugging.
//
namespace {
  // Output - The user can specify a file containing the expected output of the
  // program.  If this filename is set, it is used as the reference diff source,
  // otherwise the raw input run through an interpreter is used as the reference
  // source.
  //
  cl::opt<std::string>
  OutputFile("output", cl::desc("Specify a reference program output "
                                "(for miscompilation detection)"));
}

/// setNewProgram - If we reduce or update the program somehow, call this method
/// to update bugdriver with it.  This deletes the old module and sets the
/// specified one as the current program.
void BugDriver::setNewProgram(Module *M) {
  delete Program;
  Program = M;
}

void SwiftBugDriver::setNewProgram(swift::SILModule *M) {
  delete Program;
  Program = M;
}

/// getPassesString - Turn a list of passes into a string which indicates the
/// command line options that must be passed to add the passes.
///
std::string llvm::getPassesString(const std::vector<std::string> &Passes) {
  std::string Result;
  for (unsigned i = 0, e = Passes.size(); i != e; ++i) {
    if (i) Result += " ";
    Result += "-";
    Result += Passes[i];
  }
  return Result;
}

BugDriver::BugDriver(const char *toolname, bool find_bugs,
                     unsigned timeout, unsigned memlimit, bool use_valgrind,
                     LLVMContext& ctxt)
  : Context(ctxt), ToolName(toolname), ReferenceOutputFile(OutputFile),
    Program(nullptr), Interpreter(nullptr), SafeInterpreter(nullptr),
    cc(nullptr), run_find_bugs(find_bugs), Timeout(timeout),
    MemoryLimit(memlimit), UseValgrind(use_valgrind) {}

BugDriver::~BugDriver() {
  delete Program;
  if (Interpreter != SafeInterpreter)
    delete Interpreter;
  delete SafeInterpreter;
  delete cc;
}

SwiftBugDriver::SwiftBugDriver(const char *toolname, bool find_bugs,
                     unsigned timeout, unsigned memlimit, bool use_valgrind,
                     LLVMContext& ctxt)
  : Context(ctxt), ToolName(toolname), ReferenceOutputFile(OutputFile),
    Program(nullptr), Interpreter(nullptr), SafeInterpreter(nullptr),
    cc(nullptr), run_find_bugs(find_bugs), Timeout(timeout),
    MemoryLimit(memlimit), UseValgrind(use_valgrind) {}

SwiftBugDriver::~SwiftBugDriver() {
  delete Program;
  if (Interpreter != SafeInterpreter)
    delete Interpreter;
  delete SafeInterpreter;
  delete cc;
}

static llvm::cl::list<swift::PassKind>
Passes(llvm::cl::desc("Passes:"),
       llvm::cl::values(
#define PASS(ID, NAME, DESCRIPTION) clEnumValN(swift::PassKind::ID, NAME, DESCRIPTION),
#include "swift/SILOptimizer/PassManager/Passes.def"
       clEnumValEnd));


enum class OptGroup {
  Unknown, Diagnostics, Performance
};

static void runCommandLineSelectedPasses(swift::SILModule *Module) {
  swift::SILPassManager PM(Module);

  for (auto Pass : Passes) {
    PM.addPass(Pass);
  }
  PM.run();
}

// FIXME: SILModule cannot outlive the CompilerInvocation.
// Therefore, the CompilerInvocation should be preserved.
std::unique_ptr<swift::SILModule> parseSILFile(StringRef InputFilename,
                                               SMDiagnostic &Err,
                                               llvm::LLVMContext &Ctxt,
                                               ArrayRef<std::string> toolArgs) {
  swift::CompilerInvocation Invocation;
  bool EmitVerboseSIL = false;
  bool EnableSILSortOutput = false;
  bool DisableASTDump = true;

  swift::SourceManager SM;
  swift::DiagnosticEngine Diags(SM);
  SmallVector<const char *, 16> Args;
  std::string SDKPath;
  std::string ResourceDir;
  //Args.append(toolArgs.begin(), toolArgs.end());
  for (auto Arg = toolArgs.begin(), End = toolArgs.end(); Arg != End; ++Arg) {
    if (StringRef("-sdk") == *Arg) {
      ++Arg;
      if (Arg != End) {
        SDKPath = *Arg;
       continue;
      }
      llvm::errs() << "-sdk should be followed by a path";
    }
    if (StringRef("-resource-dir") == *Arg) {
      ++Arg;
      if (Arg != End) {
        ResourceDir = *Arg;
       continue;
      }
      llvm::errs() << "-resource-dir should be followed by a path";
    }

    Args.push_back(StringRef(*Arg).data());
  }

  Invocation.parseArgs(Args, Diags);
  // Parse toolArgs and initialize global flags from it.
  // TODO: It would be better if all those global flags are encapsulated
  // in a single data structure, which is not initialized globally, but
  // can be initialized by means of a function call which takes as a
  // parameter the set of passed command-line arguments.

/*
  Invocation.setMainExecutablePath(
      llvm::sys::fs::getMainExecutable(argv[0],
          reinterpret_cast<void *>(&anchorForGetMainExecutable)));
*/

  // Give the context the list of search paths to use for modules.
  // Invocation.setImportSearchPaths(ImportPaths);
  //Invocation.setFrameworkSearchPaths(FrameworkPaths);
  // Set the SDK path and target if given.
  if (SDKPath.empty()) {
    const char *SDKROOT = getenv("SDKROOT");
    if (SDKROOT)
      SDKPath = SDKROOT;
  }
  if (!SDKPath.empty())
    Invocation.setSDKPath(SDKPath);
  if (!ResourceDir.empty())
    Invocation.setRuntimeResourcePath(ResourceDir);
#if 0
  if (!Target.empty())
    Invocation.setTargetTriple(Target);
  Invocation.getFrontendOptions().EnableResilience = EnableResilience;
  // Set the module cache path. If not passed in we use the default swift module
  // cache.
  Invocation.getClangImporterOptions().ModuleCachePath = ModuleCachePath;
#endif
  Invocation.setParseStdlib();
  Invocation.getLangOptions().EnableAccessControl = false;
  Invocation.getLangOptions().EnableObjCAttrRequiresFoundation = false;

#if 0
  Invocation.getLangOptions().ASTVerifierProcessCount =
      ASTVerifierProcessCount;
  Invocation.getLangOptions().ASTVerifierProcessId =
      ASTVerifierProcessId;
#endif
  // Setup the SIL Options.
  swift::SILOptions &SILOpts = Invocation.getSILOptions();
#if 0
  SILOpts.InlineThreshold = SILInlineThreshold;
  SILOpts.VerifyAll = EnableSILVerifyAll;
  SILOpts.RemoveRuntimeAsserts = RemoveRuntimeAsserts;
  SILOpts.AssertConfig = AssertConfId;
  if (OptimizationGroup != OptGroup::Diagnostics)
    SILOpts.Optimization = SILOptions::SILOptMode::Optimize;
#endif

  // Load the input file.
  llvm::ErrorOr<std::unique_ptr<llvm::MemoryBuffer>> FileBufOrErr =
    llvm::MemoryBuffer::getFileOrSTDIN(InputFilename);
  if (!FileBufOrErr) {
    fprintf(stderr, "Error! Failed to open file: %s\n", InputFilename.data());
    exit(-1);
  }

  // If it looks like we have an AST, set the source file kind to SIL and the
  // name of the module to the file's name.
  Invocation.addInputBuffer(FileBufOrErr.get().get());

  swift::serialization::ExtendedValidationInfo extendedInfo;
  auto result = swift::serialization::validateSerializedAST(
      FileBufOrErr.get()->getBuffer(), &extendedInfo);
  bool HasSerializedAST = result.status == swift::serialization::Status::Valid;

  StringRef ModuleName;
  if (HasSerializedAST) {
    const StringRef Stem = ModuleName.size() ?
                             StringRef(ModuleName) :
                             llvm::sys::path::stem(InputFilename);
    Invocation.setModuleName(Stem);
    Invocation.setInputKind(swift::InputFileKind::IFK_Swift_Library);
  } else {
    const StringRef Name = ModuleName.size() ? StringRef(ModuleName) : "main";
    Invocation.setModuleName(Name);
    Invocation.setInputKind(swift::InputFileKind::IFK_SIL);
  }

  swift::CompilerInstance CI;
  swift::PrintingDiagnosticConsumer PrintDiags;
  CI.addDiagnosticConsumer(&PrintDiags);

  bool PerformWMO = false;
  if (!PerformWMO) {
    auto &FrontendOpts = Invocation.getFrontendOptions();
    if (!InputFilename.empty() && InputFilename != "-") {
      FrontendOpts.PrimaryInput = swift::SelectedInput(
          FrontendOpts.InputFilenames.size());
    } else {
      FrontendOpts.PrimaryInput = swift::SelectedInput(
          FrontendOpts.InputBuffers.size(), swift::SelectedInput::InputKind::Buffer);
    }
  }

  if (CI.setup(Invocation))
    return nullptr;

  CI.performSema();

  // If parsing produced an error, don't run any passes.
  if (CI.getASTContext().hadError())
    return nullptr;

  // Load the SIL if we have a module. We have to do this after SILParse
  // creating the unfortunate double if statement.
  if (HasSerializedAST) {
    assert(!CI.hasSILModule() &&
           "performSema() should not create a SILModule.");
    CI.setSILModule(swift::SILModule::createEmptyModule(CI.getMainModule(),
                                                 CI.getSILOptions()));
    std::unique_ptr<swift::SerializedSILLoader> SL = swift::SerializedSILLoader::create(
        CI.getASTContext(), CI.getSILModule(), nullptr);

    if (extendedInfo.isSIB())
      SL->getAllForModule(CI.getMainModule()->getName(), nullptr);
    else
      SL->getAll();
  }

  bool VerifyMode = false;
  // If we're in verify mode, install a custom diagnostic handling for
  // SourceMgr.
  if (VerifyMode)
    enableDiagnosticVerifier(CI.getSourceMgr());
  
  OptGroup OptimizationGroup = OptGroup::Performance;

  if (OptimizationGroup == OptGroup::Diagnostics) {
    runSILDiagnosticPasses(*CI.getSILModule());
  } else if (OptimizationGroup == OptGroup::Performance) {
    runSILOptimizationPasses(*CI.getSILModule());
  } else {
    runCommandLineSelectedPasses(CI.getSILModule());
  }

  bool EmitSIB = false;
  StringRef OutputFilename;
  if (EmitSIB) {
    // Output SIL in a binary form.
    llvm::SmallString<128> OutputFile;
    if (OutputFilename.size()) {
      OutputFile = OutputFilename;
    } else if (ModuleName.size()) {
      OutputFile = ModuleName;
      llvm::sys::path::replace_extension(OutputFile, swift::SIB_EXTENSION);
    } else {
      OutputFile = CI.getMainModule()->getName().str();
      llvm::sys::path::replace_extension(OutputFile, swift::SIB_EXTENSION);
    }

    swift::SerializationOptions serializationOpts;
    serializationOpts.OutputPath = OutputFile.c_str();
    serializationOpts.SerializeAllSIL = true;
    serializationOpts.IsSIB = true;

    swift::serialize(CI.getMainModule(), serializationOpts, CI.getSILModule());
  } else {
    // Output SIL in textual form.
    const StringRef OutputFile = OutputFilename.size() ?
                                   StringRef(OutputFilename) : "-";

    if (OutputFile == "-") {
      // TODO: It should not be possible that there is no output file name!
#if 0
      CI.getSILModule()->print(llvm::outs(), EmitVerboseSIL, CI.getMainModule(),
                               EnableSILSortOutput, !DisableASTDump);
#endif
    } else {
      std::error_code EC;
      llvm::raw_fd_ostream OS(OutputFile, EC, llvm::sys::fs::F_None);
      if (EC) {
        llvm::errs() << "while opening '" << OutputFile << "': "
                     << EC.message() << '\n';
        return nullptr;
      }
      CI.getSILModule()->print(OS, EmitVerboseSIL, CI.getMainModule(),
                               EnableSILSortOutput, !DisableASTDump);
    }
  }

  bool HadError = CI.getASTContext().hadError();

  // If we're in -verify mode, we've buffered up all of the generated
  // diagnostics.  Check now to ensure that they meet our expectations.
  if (VerifyMode) {
    HadError = verifyDiagnostics(CI.getSourceMgr(), CI.getInputBufferIDs());
    swift::DiagnosticEngine &diags = CI.getDiags();
    if (diags.hasFatalErrorOccurred() &&
        !Invocation.getDiagnosticOptions().ShowDiagnosticsAfterFatalError) {
      diags.resetHadAnyError();
      diags.diagnose(swift::SourceLoc(), swift::diag::verify_encountered_fatal);
      HadError = true;
    }
  }

  return std::unique_ptr<swift::SILModule>(CI.takeSILModule());
}

std::unique_ptr<swift::SILModule> llvm::parseSILInputFile(StringRef Filename,
                                             LLVMContext &Ctxt,
                                             ArrayRef<std::string> toolArgs) {
  SMDiagnostic Err;
  std::unique_ptr<swift::SILModule> Result = parseSILFile(Filename, Err, Ctxt, toolArgs);
  if (!Result) {
    Err.print("bugpoint", errs());
    return Result;
  }

  Result->verify();
  /*
  if (Result->verify()) {
  //if (verifyModule(*Result, &errs())) {
    errs() << "bugpoint: " << Filename << ": error: input module is broken!\n";
    return std::unique_ptr<swift::SILModule>();
  }
  */

  // If we don't have an override triple, use the first one to configure
  // bugpoint, or use the host triple if none provided.
  if (TargetTriple.getTriple().empty()) {
#if 0
    Triple TheTriple(Result->getTargetTriple());

    if (TheTriple.getTriple().empty())
      TheTriple.setTriple(sys::getDefaultTargetTriple());

    TargetTriple.setTriple(TheTriple.getTriple());
#endif
    //assert(0 && "Not implemented yet");
  }

  //Result->setTargetTriple(TargetTriple.getTriple()); // override the triple
  return Result;
}



std::unique_ptr<Module> llvm::parseInputFile(StringRef Filename,
                                             LLVMContext &Ctxt) {
  SMDiagnostic Err;
  std::unique_ptr<Module> Result = parseIRFile(Filename, Err, Ctxt);
  if (!Result) {
    Err.print("bugpoint", errs());
    return Result;
  }

  if (verifyModule(*Result, &errs())) {
    errs() << "bugpoint: " << Filename << ": error: input module is broken!\n";
    return std::unique_ptr<Module>();
  }

  // If we don't have an override triple, use the first one to configure
  // bugpoint, or use the host triple if none provided.
  if (TargetTriple.getTriple().empty()) {
    Triple TheTriple(Result->getTargetTriple());

    if (TheTriple.getTriple().empty())
      TheTriple.setTriple(sys::getDefaultTargetTriple());

    TargetTriple.setTriple(TheTriple.getTriple());
  }

  Result->setTargetTriple(TargetTriple.getTriple()); // override the triple
  return Result;
}

// This method takes the specified list of LLVM input files, attempts to load
// them, either as assembly or bitcode, then link them together. It returns
// true on failure (if, for example, an input bitcode file could not be
// parsed), and false on success.
//
bool BugDriver::addSources(const std::vector<std::string> &Filenames) {
  assert(!Program && "Cannot call addSources multiple times!");
  assert(!Filenames.empty() && "Must specify at least on input filename!");

  // Load the first input file.
  Program = parseInputFile(Filenames[0], Context).release();
  if (!Program) return true;

  outs() << "Read input file      : '" << Filenames[0] << "'\n";

  for (unsigned i = 1, e = Filenames.size(); i != e; ++i) {
    std::unique_ptr<Module> M = parseInputFile(Filenames[i], Context);
    if (!M.get()) return true;

    outs() << "Linking in input file: '" << Filenames[i] << "'\n";
    if (Linker::linkModules(*Program, std::move(M)))
      return true;
  }

  outs() << "*** All input ok\n";

  // All input files read successfully!
  return false;
}

bool SwiftBugDriver::addSources(const std::vector<std::string> &Filenames) {
  assert(!Program && "Cannot call addSources multiple times!");
  assert(!Filenames.empty() && "Must specify at least on input filename!");

  if (initializeExecutionEnvironment())
    return true;

#if 1
  // FIXME: Check that it is really a SILOpt
  auto silOpt = reinterpret_cast<SILOpt*>(Interpreter);
  auto toolArgs = silOpt->getToolArgs();

  std::string error;
  //silOpt->compileProgram(Filenames[0], error);
#endif
  // Load the first input file.
  Program = parseSILInputFile(Filenames[0], Context, toolArgs).release();
  if (!Program) return true;

  outs() << "Read input file      : '" << Filenames[0] << "'\n";

  for (unsigned i = 1, e = Filenames.size(); i != e; ++i) {
#if 0
    std::unique_ptr<swift::SILModule> M = parseSILInputFile(Filenames[i], Context);
    if (!M.get()) return true;

    outs() << "Linking in input file: '" << Filenames[i] << "'\n";
    if (Linker::linkModules(*Program, std::move(M)))
      return true;
#endif
    assert(0 && "Not implemented yet");
  }

  outs() << "*** All input ok\n";

  // All input files read successfully!
  return false;
}



/// run - The top level method that is invoked after all of the instance
/// variables are set up from command line arguments.
///
bool BugDriver::run(std::string &ErrMsg) {
  if (run_find_bugs) {
    // Rearrange the passes and apply them to the program. Repeat this process
    // until the user kills the program or we find a bug.
    return runManyPasses(PassesToRun, ErrMsg);
  }

  // If we're not running as a child, the first thing that we must do is
  // determine what the problem is. Does the optimization series crash the
  // compiler, or does it produce illegal code?  We make the top-level
  // decision by trying to run all of the passes on the input program,
  // which should generate a bitcode file.  If it does generate a bitcode
  // file, then we know the compiler didn't crash, so try to diagnose a
  // miscompilation.
  if (!PassesToRun.empty()) {
    outs() << "Running selected passes on program to test for crash: ";
    if (runPasses(Program, PassesToRun))
      return debugOptimizerCrash();
  }

  // Set up the execution environment, selecting a method to run LLVM bitcode.
  if (initializeExecutionEnvironment()) return true;

  // Test to see if we have a code generator crash.
  outs() << "Running the code generator to test for a crash: ";
  std::string Error;
  compileProgram(Program, &Error);
  if (!Error.empty()) {
    outs() << Error;
    return debugCodeGeneratorCrash(ErrMsg);
  }
  outs() << '\n';

  // Run the raw input to see where we are coming from.  If a reference output
  // was specified, make sure that the raw output matches it.  If not, it's a
  // problem in the front-end or the code generator.
  //
  bool CreatedOutput = false;
  if (ReferenceOutputFile.empty()) {
    outs() << "Generating reference output from raw program: ";
    if (!createReferenceFile(Program)) {
      return debugCodeGeneratorCrash(ErrMsg);
    }
    CreatedOutput = true;
  }

  // Make sure the reference output file gets deleted on exit from this
  // function, if appropriate.
  std::string ROF(ReferenceOutputFile);
  FileRemover RemoverInstance(ROF, CreatedOutput && !SaveTemps);

  // Diff the output of the raw program against the reference output.  If it
  // matches, then we assume there is a miscompilation bug and try to
  // diagnose it.
  outs() << "*** Checking the code generator...\n";
  bool Diff = diffProgram(Program, "", "", false, &Error);
  if (!Error.empty()) {
    errs() << Error;
    return debugCodeGeneratorCrash(ErrMsg);
  }
  if (!Diff) {
    outs() << "\n*** Output matches: Debugging miscompilation!\n";
    debugMiscompilation(&Error);
    if (!Error.empty()) {
      errs() << Error;
      return debugCodeGeneratorCrash(ErrMsg);
    }
    return false;
  }

  outs() << "\n*** Input program does not match reference diff!\n";
  outs() << "Debugging code generator problem!\n";
  bool Failure = debugCodeGenerator(&Error);
  if (!Error.empty()) {
    errs() << Error;
    return debugCodeGeneratorCrash(ErrMsg);
  }
  return Failure;
}

bool SwiftBugDriver::run(std::string &ErrMsg) {
  if (run_find_bugs) {
    // Rearrange the passes and apply them to the program. Repeat this process
    // until the user kills the program or we find a bug.
    return runManyPasses(PassesToRun, ErrMsg);
  }

  // If we're not running as a child, the first thing that we must do is
  // determine what the problem is. Does the optimization series crash the
  // compiler, or does it produce illegal code?  We make the top-level
  // decision by trying to run all of the passes on the input program,
  // which should generate a bitcode file.  If it does generate a bitcode
  // file, then we know the compiler didn't crash, so try to diagnose a
  // miscompilation.
  if (!PassesToRun.empty()) {
    outs() << "Running selected passes on program to test for crash: ";
    if (runPasses(Program, PassesToRun))
      return debugOptimizerCrash();
  }

  // Set up the execution environment, selecting a method to run LLVM bitcode.
  if (initializeExecutionEnvironment()) return true;

  // Test to see if we have a code generator crash.
  outs() << "Running the code generator to test for a crash: ";
  std::string Error;
  compileProgram(Program, &Error);
  if (!Error.empty()) {
    outs() << Error;
    return debugCodeGeneratorCrash(ErrMsg);
  }
  outs() << '\n';

  // Run the raw input to see where we are coming from.  If a reference output
  // was specified, make sure that the raw output matches it.  If not, it's a
  // problem in the front-end or the code generator.
  //
  bool CreatedOutput = false;
  if (ReferenceOutputFile.empty()) {
    outs() << "Generating reference output from raw program: ";
    if (!createReferenceFile(Program)) {
      return debugCodeGeneratorCrash(ErrMsg);
    }
    CreatedOutput = true;
  }

  // Make sure the reference output file gets deleted on exit from this
  // function, if appropriate.
  std::string ROF(ReferenceOutputFile);
  FileRemover RemoverInstance(ROF, CreatedOutput && !SaveTemps);

  // Diff the output of the raw program against the reference output.  If it
  // matches, then we assume there is a miscompilation bug and try to
  // diagnose it.
  outs() << "*** Checking the code generator...\n";
  bool Diff = diffProgram(Program, "", "", false, &Error);
  if (!Error.empty()) {
    errs() << Error;
    return debugCodeGeneratorCrash(ErrMsg);
  }
  if (!Diff) {
    outs() << "\n*** Output matches: Debugging miscompilation!\n";
    debugMiscompilation(&Error);
    if (!Error.empty()) {
      errs() << Error;
      return debugCodeGeneratorCrash(ErrMsg);
    }
    return false;
  }

  outs() << "\n*** Input program does not match reference diff!\n";
  outs() << "Debugging code generator problem!\n";
  bool Failure = debugCodeGenerator(&Error);
  if (!Error.empty()) {
    errs() << Error;
    return debugCodeGeneratorCrash(ErrMsg);
  }
  return Failure;
}

void llvm::PrintFunctionList(const std::vector<Function*> &Funcs) {
  unsigned NumPrint = Funcs.size();
  if (NumPrint > 10) NumPrint = 10;
  for (unsigned i = 0; i != NumPrint; ++i)
    outs() << " " << Funcs[i]->getName();
  if (NumPrint < Funcs.size())
    outs() << "... <" << Funcs.size() << " total>";
  outs().flush();
}

void llvm::PrintFunctionList(const std::vector<swift::SILFunction*> &Funcs) {
  unsigned NumPrint = Funcs.size();
  if (NumPrint > 10) NumPrint = 10;
  for (unsigned i = 0; i != NumPrint; ++i)
    outs() << " " << Funcs[i]->getName();
  if (NumPrint < Funcs.size())
    outs() << "... <" << Funcs.size() << " total>";
  outs().flush();
}

void llvm::PrintGlobalVariableList(const std::vector<GlobalVariable*> &GVs) {
  unsigned NumPrint = GVs.size();
  if (NumPrint > 10) NumPrint = 10;
  for (unsigned i = 0; i != NumPrint; ++i)
    outs() << " " << GVs[i]->getName();
  if (NumPrint < GVs.size())
    outs() << "... <" << GVs.size() << " total>";
  outs().flush();
}
