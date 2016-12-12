//===--- SpecializationMangler.h - mangling of specializations --*- C++ -*-===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2016 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SILOPTIMIZER_UTILS_SPECIALIZATIONMANGLER_H
#define SWIFT_SILOPTIMIZER_UTILS_SPECIALIZATIONMANGLER_H

#include "swift/Basic/Demangler.h"
#include "swift/Basic/NullablePtr.h"
#include "swift/AST/ASTMangler.h"
#include "swift/SIL/SILLinkage.h"
#include "swift/SIL/SILFunction.h"

namespace swift {
namespace NewMangling {

enum class SpecializationKind : uint8_t {
  Generic,
  NotReAbstractedGeneric,
  FunctionSignature,
};
  
/// Inject SpecializationPass into the Mangle namespace.
using SpecializationPass = Demangle::SpecializationPass;

/// The base class for specialization mangles.
class SpecializationMangler : public NewMangling::ASTMangler {
protected:
  /// The specialization pass.
  SpecializationPass Pass;

  IsFragile_t Fragile;

  /// The original function which is specialized.
  SILFunction *Function;

  llvm::SmallVector<char, 32> ArgOpStorage;
  llvm::raw_svector_ostream ArgOpBuffer;

  CanSILFunctionType CanSILFnTy;
protected:
  SpecializationMangler(SpecializationPass P, IsFragile_t Fragile,
                        SILFunction *F)
      : Pass(P), Fragile(Fragile), Function(F), ArgOpBuffer(ArgOpStorage) {}

  SpecializationMangler(SpecializationPass P, IsFragile_t Fragile,
                        SILFunction *F, CanSILFunctionType CanSILFnTy)
      : Pass(P), Fragile(Fragile), Function(F), ArgOpBuffer(ArgOpStorage),
        CanSILFnTy(CanSILFnTy) {}


  SILFunction *getFunction() const { return Function; }
  CanSILFunctionType getSILFunctionType() const { return CanSILFnTy; }

  void beginMangling();

  /// Finish the mangling of the symbol and return the mangled name.
  std::string finalize();

  void appendSpecializationOperator(StringRef Op) {
    appendOperator(Op, StringRef(ArgOpStorage.data(), ArgOpStorage.size()));
  }
};

// The mangler for specialized generic functions.
class GenericSpecializationMangler : public SpecializationMangler {

  ArrayRef<Substitution> Subs;

public:

  bool isReAbstracted;

  GenericSpecializationMangler(SILFunction *F, CanSILFunctionType CanSILFnTy,
                               IsFragile_t Fragile, bool isReAbstracted)
      : SpecializationMangler(SpecializationPass::GenericSpecializer, Fragile,
                              F, CanSILFnTy),
        isReAbstracted(isReAbstracted) {}

  std::string mangle();
};

// The mangler for functions where arguments are specialized.
class FunctionSignatureSpecializationMangler : public SpecializationMangler {

  using ReturnValueModifierIntBase = uint16_t;
  enum class ReturnValueModifier : ReturnValueModifierIntBase {
    // Option Space 4 bits (i.e. 16 options).
    Unmodified=0,
    First_Option=0, Last_Option=31,

    // Option Set Space. 12 bits (i.e. 12 option).
    Dead=32,
    OwnedToUnowned=64,
    First_OptionSetEntry=32, LastOptionSetEntry=32768,
  };

  // We use this private typealias to make it easy to expand ArgumentModifier's
  // size if we need to.
  using ArgumentModifierIntBase = uint16_t;
  enum class ArgumentModifier : ArgumentModifierIntBase {
    // Option Space 4 bits (i.e. 16 options).
    Unmodified=0,
    ConstantProp=1,
    ClosureProp=2,
    BoxToValue=3,
    BoxToStack=4,
    First_Option=0, Last_Option=31,

    // Option Set Space. 12 bits (i.e. 12 option).
    Dead=32,
    OwnedToGuaranteed=64,
    SROA=128,
    First_OptionSetEntry=32, LastOptionSetEntry=32768,
  };

  using ArgInfo = std::pair<ArgumentModifierIntBase,
                            NullablePtr<SILInstruction>>;
  llvm::SmallVector<ArgInfo, 8> Args;

  ReturnValueModifierIntBase ReturnValue;

public:
  FunctionSignatureSpecializationMangler(SpecializationPass Pass,
                                         IsFragile_t Fragile,
                                         SILFunction *F);
  void setArgumentConstantProp(unsigned ArgNo, LiteralInst *LI);
  void setArgumentClosureProp(unsigned ArgNo, PartialApplyInst *PAI);
  void setArgumentClosureProp(unsigned ArgNo, ThinToThickFunctionInst *TTTFI);
  void setArgumentDead(unsigned ArgNo);
  void setArgumentOwnedToGuaranteed(unsigned ArgNo);
  void setArgumentSROA(unsigned ArgNo);
  void setArgumentBoxToValue(unsigned ArgNo);
  void setArgumentBoxToStack(unsigned ArgNo);
  void setReturnValueOwnedToUnowned();

  std::string mangle();
  
private:
  void mangleConstantProp(LiteralInst *LI);
  void mangleClosureProp(SILInstruction *Inst);
  void mangleArgument(ArgumentModifierIntBase ArgMod,
                      NullablePtr<SILInstruction> Inst);
  void mangleReturnValue(ReturnValueModifierIntBase RetMod);
};

} // end namespace NewMangling
} // end namespace swift

#endif
