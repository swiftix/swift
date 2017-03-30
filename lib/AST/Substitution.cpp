//===--- Substitution.cpp - Type substitutions ----------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2017 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
//  This file implements the Substitution class and operations on it.
//
//===----------------------------------------------------------------------===//

#include "swift/AST/Substitution.h"

#include "swift/AST/ASTContext.h"
#include "swift/AST/GenericEnvironment.h"
#include "swift/AST/Module.h"
#include "swift/AST/ProtocolConformance.h"
#include "swift/AST/SubstitutionMap.h"
#include "swift/AST/Types.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Debug.h"

using namespace swift;

bool Substitution::operator==(const Substitution &other) const {
  // The archetypes may be missing, but we can compare them directly
  // because archetypes are always canonical.
  return
    Replacement->isEqual(other.Replacement) &&
    Conformance.equals(other.Conformance);
}

Substitution::Substitution(Type Replacement,
                           ArrayRef<ProtocolConformanceRef> Conformance)
  : Replacement(Replacement), Conformance(Conformance)
{
  // The replacement type must be materializable.
  assert(Replacement->isMaterializable()
         && "cannot substitute with a non-materializable type");
#ifndef NDEBUG
  if (Replacement->isTypeParameter() || Replacement->is<ArchetypeType>() ||
      Replacement->isTypeVariableOrMember() ||
      Replacement->is<UnresolvedType>() || Replacement->hasError())
    return;
  // Check conformances of a concrete replacement type.
  for (auto C : Conformance) {
    // An existential type can have an abstract conformance to
    // AnyObject or an @objc protocol.
    if (C.isAbstract() && Replacement->isExistentialType()) {
      auto *proto = C.getRequirement();
      assert((proto->isSpecificProtocol(KnownProtocolKind::AnyObject) ||
              proto->isObjC()) &&
             "an existential type can conform only to AnyObject or an "
             "@objc-protocol");
      continue;
    }
    // All of the conformances should be concrete.
    if (!C.isConcrete()) {
      llvm::dbgs() << "Concrete replacement type:\n";
      Replacement->dump(llvm::dbgs());
      llvm::dbgs() << "SubstitutionMap:\n";
      dump(llvm::dbgs());
    }
    assert(C.isConcrete() && "Conformance should be concrete");
  }
#endif
}
