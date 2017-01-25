//===--- ResilienceDiagnostics.cpp - Resilience Inlineability Diagnostics -===//
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
// This file implements diagnostics for @inlineable.
//
//===----------------------------------------------------------------------===//

#include "TypeChecker.h"
#include "swift/AST/Attr.h"
#include "swift/AST/Decl.h"
#include "swift/AST/Initializer.h"
#include "swift/AST/DeclContext.h"
using namespace swift;

enum FragileFunctionKind : unsigned {
  Transparent,
  InlineAlways,
  Inlineable,
  DefaultArgument
};

bool isFragile(const ValueDecl *VD);
bool isFragile(const DeclContext *DC);

static bool isFragileWhitelistedTypeName(StringRef Name, const ValueDecl *VD) {
  if (!VD->getDeclContext()->getParentModule()->isStdlibModule())
    return false;

  // Nested types cannot be @_inlineable or @_fixed_layout.
  //if (VD->getDeclContext()->isTypeContext())
  if (!VD->getDeclContext()->isModuleScopeContext())
    return false;

  return Name.contains("Array") || Name.contains("StringRefliceBuffer") ||
         Name == "_DependenceToken" || Name == "_IgnorePointer" ||
         Name == "AutoreleasingUnsafeMutablePointer" ||
         // There is a bug related to the default value initializer
         // function_ref
         // UnsafeMutableRawBufferPointer.Iterator.(_position).(variable
         // initialization expression)
         Name == "UnsafeMutableRawBufferPointer" ||
         Name == "_ClosedRangeIndexRepresentation" || Name == "LazyMapIterator";
}

static bool isFragileWhitelistedDeclName(StringRef Name, const ValueDecl *VD) {
  if (!VD->getDeclContext()->getParentModule()->isStdlibModule())
    return false;

  return Name == "_InitializeMemoryFromCollection" ||
         Name == "_makeSwiftNSFastEnumerationState" ||
         Name == "_isValidArraySubscript" || Name == "_isValidArrayIndex" ||
         Name == "_isKnownUniquelyReferencedOrPinned" ||
         Name == "_rawPointerToString" || Name == "_stdlib_NSArray_getObjects";
}

bool isFragile(const DeclContext *DC) {
  for (; DC; DC = DC->getParent()) {
    if (auto VD = dyn_cast_or_null<ValueDecl>(
            DC->getInnermostDeclarationDeclContext())) {
      return isFragile(VD);
      //if (isFragileWhitelistedName(VD->getNameStr()))
      //  return ResilienceExpansion::Minimal;
    }

    if (DC->isTypeContext()) {
      auto *NTE = DC->getAsNominalTypeOrNominalTypeExtensionContext();
      if (NTE) {
        auto Name = NTE->getNameStr();
        if (isFragileWhitelistedTypeName(Name, NTE)) {
          return true;
        }
      }
    }
  }
  return false;
}

bool isFragile(const ValueDecl *VD) {
  auto *NTE = dyn_cast<NominalTypeDecl>(VD);
  if (isa<NominalTypeDecl>(VD) || isa<ExtensionDecl>(VD)) {
    auto Name = VD->getNameStr();
    if (isFragileWhitelistedTypeName(Name, VD)) {
      return true;
    }
  }

  // If it is inside a fragile context, it is fragile.
  if (isFragile(VD->getDeclContext()))
    return true;

  // Check if it is a whitelisted declaration.
  if (isFragileWhitelistedDeclName(VD->getNameStr(), VD))
    return true;
  return false;
}

FragileFunctionKind getFragileFunctionKind(const DeclContext *DC) {
  for (; DC->isLocalContext(); DC = DC->getParent()) {
    if (auto *DAI = dyn_cast<DefaultArgumentInitializer>(DC))
      if (DAI->getResilienceExpansion() == ResilienceExpansion::Minimal)
        return FragileFunctionKind::DefaultArgument;

    if (auto *AFD = dyn_cast<AbstractFunctionDecl>(DC)) {
      // If the function is a nested function, we will serialize its body if
      // we serialize the parent's body.
      if (AFD->getDeclContext()->isLocalContext())
        continue;

      // Bodies of public transparent and always-inline functions are
      // serialized, so use conservative access patterns.
      if (AFD->isTransparent())
        return FragileFunctionKind::Transparent;

      if (AFD->getAttrs().hasAttribute<InlineableAttr>())
        return FragileFunctionKind::Inlineable;

      if (auto attr = AFD->getAttrs().getAttribute<InlineAttr>())
        if (attr->getKind() == InlineKind::Always)
          return FragileFunctionKind::InlineAlways;

      // If a property or subscript is @_inlineable, the accessors are
      // @_inlineable also.
      if (auto FD = dyn_cast<FuncDecl>(AFD))
        if (auto *ASD = FD->getAccessorStorageDecl())
          if (ASD->getAttrs().getAttribute<InlineableAttr>())
            return FragileFunctionKind::Inlineable;
    }
    // This is a hack for benchmarking purposes. Mark all
    // whitelisted functions as fragile. The set of whitelisted
    // functions may include all functions from Swift.Array and all related
    // types like ArraySlice, ArrayBuffer, etc.
    // All Array-related types are supposed to be fragile.
    if (isFragile(DC->getParent())) {
#if 0
          DeclAttributes &Attrs = AFD->getAttrs();
          // Make this function @_inlinable
          if (!Attrs.hasAttribute<InlineableAttr>())
            Attrs.add(
                SimpleDeclAttr<DAK_Inlineable>(/* IsImplicit */ true));
          // If it is an internal function, make it also @_versioned.
          if (AFD->getEffectiveAccess() < Accessibility::Public)
            Attrs.add(
                SimpleDeclAttr<DAK_Versioned>(/* IsImplicit */ true));
#endif
        return FragileFunctionKind::Inlineable;
    }
  }

  if (isFragile(DC))
    return FragileFunctionKind::Inlineable;

  llvm_unreachable("Context is not nested inside a fragile function");
}

void TypeChecker::diagnoseInlineableLocalType(const NominalTypeDecl *NTD) {
  auto *DC = NTD->getDeclContext();
  auto expansion = DC->getResilienceExpansion();
  if (expansion == ResilienceExpansion::Minimal) {
    if (DC->isTypeContext())
      return;
    auto expansion = DC->getResilienceExpansion();
    diagnose(NTD, diag::local_type_in_inlineable_function,
             NTD->getFullName(), getFragileFunctionKind(DC));
  }
}

bool TypeChecker::diagnoseInlineableDeclRef(SourceLoc loc,
                                            const ValueDecl *D,
                                            const DeclContext *DC) {
  auto expansion = DC->getResilienceExpansion();
  if (expansion == ResilienceExpansion::Minimal) {
    if (!isa<GenericTypeParamDecl>(D) &&
        // Protocol requirements are not versioned because there's no
        // global entry point
        !(isa<ProtocolDecl>(D->getDeclContext()) && isRequirement(D)) &&
        // !isa<AssociatedTypeDecl>(D) &&
        // FIXME: Figure out what to do with typealiases
        !isa<TypeAliasDecl>(D) &&
        !D->getDeclContext()->isLocalContext() &&
        D->hasAccessibility()) {
      if (D->getEffectiveAccess() < Accessibility::Public) {
        diagnose(loc, diag::resilience_decl_unavailable,
                 D->getDescriptiveKind(), D->getFullName(),
                 D->getFormalAccess(), getFragileFunctionKind(DC));
        diagnose(D, diag::resilience_decl_declared_here,
                 D->getDescriptiveKind(), D->getFullName());
        return true;
      }
    }
  }

  // Internal declarations referenced from non-inlineable contexts are OK.
  if (expansion == ResilienceExpansion::Maximal)
    return false;

  // Local declarations are OK.
  if (D->getDeclContext()->isLocalContext())
    return false;

  // Type parameters are OK.
  if (isa<AbstractTypeParamDecl>(D))
    return false;

  // Public declarations are OK.
  if (D->getEffectiveAccess() >= Accessibility::Public)
    return false;

  // Enum cases are handled as part of their containing enum.
  if (isa<EnumElementDecl>(D))
    return false;
    
  // Protocol requirements are not versioned because there's no
  // global entry point.
  if (isa<ProtocolDecl>(D->getDeclContext()) && isRequirement(D))
    return false;

  // FIXME: Figure out what to do with typealiases
  if (isa<TypeAliasDecl>(D))
    return false;

  diagnose(loc, diag::resilience_decl_unavailable,
           D->getDescriptiveKind(), D->getFullName(),
           D->getFormalAccess(), getFragileFunctionKind(DC));
  diagnose(D, diag::resilience_decl_declared_here,
           D->getDescriptiveKind(), D->getFullName());
  return true;
}

void TypeChecker::diagnoseResilientValueConstructor(ConstructorDecl *ctor) {
  auto nominalDecl = ctor->getDeclContext()
    ->getAsNominalTypeOrNominalTypeExtensionContext();

  bool isDelegating =
      (ctor->getDelegatingOrChainedInitKind(&Diags) ==
       ConstructorDecl::BodyInitKind::Delegating);

  if (!isDelegating &&
      !nominalDecl->hasFixedLayout(ctor->getParentModule(),
                                   ctor->getResilienceExpansion())) {
    if (ctor->getResilienceExpansion() == ResilienceExpansion::Minimal) {
      // An @_inlineable designated initializer defined in a resilient type
      // cannot initialize stored properties directly, and must chain to
      // another initializer.
      diagnose(ctor->getLoc(),
               diag::designated_init_inlineable_resilient,
               ctor->getDeclContext()->getDeclaredInterfaceType(),
               getFragileFunctionKind(ctor));
    } else {
      // A designated initializer defined on an extension of a resilient
      // type from a different resilience domain cannot initialize stored
      // properties directly, and must chain to another initializer.
      diagnose(ctor->getLoc(),
               diag::designated_init_in_extension_resilient,
               ctor->getDeclContext()->getDeclaredInterfaceType());
    }
  }
}
