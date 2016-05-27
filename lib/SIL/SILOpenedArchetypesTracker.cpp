//==- SILOpenedArchetypeTracker.cpp - Track opened archetypes  ---*- C++ -*-==//
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

#include "swift/SIL/SILOpenedArchetypesTracker.h"

using namespace swift;

SILValue getEmptyTypeDef(SILType Ty);

// Register archetypes opened by a given instruction.
// Can be used to incrementally populate the mapping, e.g.
// if it is done when performing a scan of all instructions
// inside a function.
void SILOpenedArchetypesTracker::registerOpenedArchetypes(
    const SILInstruction *I) {
  assert((!I->getParent() || I->getFunction() == &F) &&
         "Instruction does not belong to a proper SILFunction");
  auto Archetype = getOpenedArchetypeOf(I);
  if (Archetype)
    addOpenedArchetypeDef(Archetype, I);
}

// Register opened archetypes whose definitions are referenced by
// the typedef operands of this instruction.
void SILOpenedArchetypesTracker::registerUsedOpenedArchetypes(
    const SILInstruction *I) {
  assert((!I->getParent() || I->getFunction() == &F) &&
         "Instruction does not belong to a proper SILFunction");
  for (auto &Op : I->getTypeDefOperands()) {
    auto TypeDef = Op.get();
    assert(isa<SILInstruction>(TypeDef) &&
           "typedef operand should refer to a SILInstruction");
    addOpenedArchetypeDef(getOpenedArchetypeOf(cast<SILInstruction>(TypeDef)),
                          TypeDef);
  }
}

// Unregister archetypes opened by a given instruction.
// Should be only called when this instruction is to be removed.
void SILOpenedArchetypesTracker::unregisterOpenedArchetypes(
    const SILInstruction *I) {
  assert(I->getFunction() == &F &&
         "Instruction does not belong to a proper SILFunction");
  auto Archetype = getOpenedArchetypeOf(I);
  if (Archetype)
    removeOpenedArchetypeDef(Archetype, I);
}

void SILOpenedArchetypesTracker::handleDeleteNotification(
    swift::ValueBase *Value) {
  if (auto I = dyn_cast<SILInstruction>(Value))
    if (I->getFunction() == &F)
      unregisterOpenedArchetypes(I);
}

/// Find an opened archetype defined by an instruction.
/// \returns The found archetype or empty type otherwise.
CanType swift::getOpenedArchetypeOf(const SILInstruction *I) {
  if (isa<OpenExistentialAddrInst>(I) || isa<OpenExistentialRefInst>(I) ||
      isa<OpenExistentialBoxInst>(I) || isa<OpenExistentialMetatypeInst>(I)) {
    auto Ty = getOpenedArchetypeOf(I->getType().getSwiftRValueType());
    assert(Ty->isOpenedExistential() && "Type should be an opened archetype");
    return Ty;
  }

  return CanType();
}

CanType swift::getOpenedArchetypeOf(CanType Ty) {
  if (!Ty)
    return CanType();
  while (auto MetaTy = dyn_cast<AnyMetatypeType>(Ty)) {
    Ty = MetaTy->getInstanceType().getCanonicalTypeOrNull();
  }
  if (Ty->isOpenedExistential())
    return Ty;
  return CanType();
}

/// Return the defintion of an opened archetype.
/// It it is an opened archetype, but its definition is not known
/// yet, return a SILUndef with the type of this opened archetype
/// Otehrwise return a SILUndef of non-archetype type.
SILValue
swift::getOpenedArchetypeDef(SILType SILTy, SILModule &M,
                             SILOpenedArchetypesTracker *OpenedArchetypes) {
  auto Ty = SILTy.getSwiftRValueType();
  Ty = getOpenedArchetypeOf(Ty);
  if (Ty && Ty->isOpenedExistential()) {
    // Lookup the definition and return it.
    if (OpenedArchetypes) {
      auto Def = OpenedArchetypes->getOpenedArchetypeDef(Ty);
      if (Def)
        return Def;
    }
    // Undef, whose type is the opened archetype.
    // It means that it needs to be replaced by a proper
    // reference to a definition later.
    return getUndefValue(M.Types.getLoweredType(Ty));
  }
  // This means that the type is not an opened archetype.
  return getEmptyTypeDef(SILTy);
}

