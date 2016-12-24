//===--- SubstitutionMap.cpp - Type substitution map ----------------------===//
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
//
// This file defines the SubstitutionMap class.
//
//===----------------------------------------------------------------------===//

#include "swift/AST/ASTContext.h"
#include "swift/AST/SubstitutionMap.h"
#include "swift/AST/Decl.h"
#include "swift/AST/ProtocolConformance.h"
#include "swift/AST/Types.h"

using namespace swift;

Optional<ProtocolConformanceRef> SubstitutionMap::
lookupConformance(ProtocolDecl *proto,
                  ArrayRef<ProtocolConformanceRef> conformances) const {
  for (ProtocolConformanceRef found : conformances) {
    auto foundProto = found.getRequirement();
    if (foundProto == proto)
      return found;
    if (foundProto->inheritsFrom(proto))
      return found.getInherited(proto);
  }

  return None;
}

template<typename Fn>
Optional<ProtocolConformanceRef>
SubstitutionMap::forEachParent(CanType type, Fn fn) const {
  auto foundParents = parentMap.find(type.getPointer());
  if (foundParents != parentMap.end()) {
    for (auto parent : foundParents->second) {
      if (auto result = fn(parent.first, parent.second))
        return result;
    }
  }

  if (auto archetypeType = dyn_cast<ArchetypeType>(type))
    if (auto *parent = archetypeType->getParent())
      return fn(CanType(parent), archetypeType->getAssocType());

  if (auto memberType = dyn_cast<DependentMemberType>(type))
    return fn(CanType(memberType->getBase()), memberType->getAssocType());

  return None;
}

Optional<ProtocolConformanceRef>
SubstitutionMap::lookupConformance(CanType type,
                                   ProtocolDecl *proto) const {
  // Check for conformances for the type that apply to the original
  // substituted archetype.
  auto foundReplacement = conformanceMap.find(type.getPointer());
  if (foundReplacement != conformanceMap.end()) {
    auto substReplacement = foundReplacement->second;
    if (auto conformance = lookupConformance(proto, substReplacement))
      return conformance;
  }

  // Check if we have substitutions from one of our parent types.
  return forEachParent(type, [&](CanType parent, AssociatedTypeDecl *assocType)
      -> Optional<ProtocolConformanceRef> {

    auto *parentProto = assocType->getProtocol();
    auto conformance = lookupConformance(parent, parentProto);

    if (!conformance)
      return None;

    if (!conformance->isConcrete())
      return ProtocolConformanceRef(proto);

    auto sub = conformance->getConcrete()->getTypeWitnessSubstAndDecl(
        assocType, nullptr).first;

    return lookupConformance(proto, sub.getConformances());
  });
}

void SubstitutionMap::
addSubstitution(CanType type, Type replacement) {
  assert(replacement);
  auto result = subMap.insert(std::make_pair(type->castTo<SubstitutableType>(),
                                             replacement));
  assert(result.second);
  (void) result;
}

void SubstitutionMap::
addConformances(CanType type, ArrayRef<ProtocolConformanceRef> conformances) {
  if (conformances.empty())
    return;

  auto result = conformanceMap.insert(
      std::make_pair(type.getPointer(), conformances));
  assert(result.second);
  (void) result;
}

ArrayRef<ProtocolConformanceRef> SubstitutionMap::
getConformances(CanType type) const {
  auto known = conformanceMap.find(type.getPointer());
  if (known == conformanceMap.end()) return { };
  return known->second;
}

void SubstitutionMap::
addParent(CanType type, CanType parent, AssociatedTypeDecl *assocType) {
  assert(type && parent && assocType);
  parentMap[type.getPointer()].push_back(std::make_pair(parent, assocType));
}

SubstitutionMap
SubstitutionMap::getOverrideSubstitutions(const ValueDecl *baseDecl,
                                          const ValueDecl *derivedDecl,
                                          Optional<SubstitutionMap> derivedSubs,
                                          LazyResolver *resolver) {
  auto *baseClass = baseDecl->getDeclContext()
      ->getAsClassOrClassExtensionContext();
  auto *derivedClass = derivedDecl->getDeclContext()
      ->getAsClassOrClassExtensionContext();

  auto *baseSig = baseDecl->getInnermostDeclContext()
      ->getGenericSignatureOfContext();
  auto *derivedSig = derivedDecl->getInnermostDeclContext()
      ->getGenericSignatureOfContext();

  return getOverrideSubstitutions(baseClass, derivedClass,
                                  baseSig, derivedSig,
                                  derivedSubs,
                                  resolver);
}

SubstitutionMap
SubstitutionMap::getOverrideSubstitutions(const ClassDecl *baseClass,
                                          const ClassDecl *derivedClass,
                                          GenericSignature *baseSig,
                                          GenericSignature *derivedSig,
                                          Optional<SubstitutionMap> derivedSubs,
                                          LazyResolver *resolver) {
  SubstitutionMap subMap;

  if (baseSig == nullptr)
    return subMap;

  unsigned minDepth = 0;

  // Get the substitutions for the self type.
  if (auto *genericSig = baseClass->getGenericSignature()) {
    auto derivedClassTy = derivedClass->getDeclaredInterfaceType();
    if (derivedSubs)
      derivedClassTy = derivedClassTy.subst(*derivedSubs);
    auto baseClassTy = derivedClassTy->getSuperclassForDecl(baseClass, resolver);

    auto *M = baseClass->getParentModule();
    auto subs = baseClassTy->gatherAllSubstitutions(M, resolver);
    genericSig->getSubstitutionMap(subs, subMap);

    minDepth = genericSig->getGenericParams().back()->getDepth() + 1;
  }

  // Map the innermost generic parameters of the derived function to
  // the base.
  auto &ctx = baseClass->getASTContext();

  auto baseParams = baseSig->getInnermostGenericParams();
  if (baseParams.back()->getDepth() >= minDepth) {
    assert(derivedSig);
    auto derivedParams = derivedSig->getInnermostGenericParams();

    assert(baseParams.size() == derivedParams.size());

    for (unsigned i = 0, e = derivedParams.size(); i < e; i++) {
      auto paramTy = baseParams[i]->getCanonicalType()
          ->castTo<GenericTypeParamType>();
      assert(paramTy->getDepth() >= minDepth);
      Type replacementTy = derivedParams[i];
      if (derivedSubs)
        replacementTy = replacementTy.subst(*derivedSubs);
      subMap.addSubstitution(paramTy->getCanonicalType(),
                             replacementTy);
    }

    auto isRootedInInnermostParameter = [&](Type t) -> bool {
      while (auto *dmt = t->getAs<DependentMemberType>())
        t = dmt->getBase();
      return t->castTo<GenericTypeParamType>()->getDepth() >= minDepth;
    };

    // Add trivial conformances for the above.
    // FIXME: This should be less awkward.
    baseSig->enumeratePairedRequirements(
      [&](Type t, ArrayRef<Requirement> reqs) -> bool {
        auto canTy = t->getCanonicalType();

        if (isRootedInInnermostParameter(t)) {
          auto conformances =
              ctx.AllocateUninitialized<ProtocolConformanceRef>(
                  reqs.size());
          for (unsigned i = 0, e = reqs.size(); i < e; i++) {
            auto reqt = reqs[i];
            assert(reqt.getKind() == RequirementKind::Conformance);
            auto *proto = reqt.getSecondType()
                ->castTo<ProtocolType>()->getDecl();
            if (derivedSubs)
              conformances[i] = *derivedSubs->lookupConformance(canTy, proto);
            else
              conformances[i] = ProtocolConformanceRef(proto);
          }

          subMap.addConformances(canTy, conformances);
        }

        return false;
    });
  }

  return subMap;
}

void SubstitutionMap::dump() const {
  llvm::errs() << "\nSubstitution map:\n";
  for (auto pair : getMap()) {
    llvm::errs() << "\n\nOriginal type:\n";
    pair.first->dump();
    llvm::errs() << "Substituted type:\n";
    pair.second->dump();
  }

  llvm::errs() << "Conformances:\n";
  for (auto &pair : conformanceMap) {
    llvm::errs() << "\n\type:\n";
    pair.first->dump();
    llvm::errs() << "Conformance of this type:\n";
    for (auto &C : pair.second) {
      llvm::errs() << "Conformance:\n";
      C.dump();
    }
  }

  llvm::errs() << "Parents:\n";
  for (auto &pair : parentMap) {
    llvm::errs() << "\n\type:\n";
    pair.first->dump();
    llvm::errs() << "Parents of this type:\n";
    for (auto &P : pair.second) {
      llvm::errs() << "Parent:\n";
      llvm::errs() << "Type:\n";
      P.first.dump();
      llvm::errs() << "Decl:\n";
      P.second->dump();
    }
  }
}
