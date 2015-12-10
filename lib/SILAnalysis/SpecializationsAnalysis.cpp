//===------------- Specializations.cpp - SIL Alias Analysis ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "sil-specializations-analysis"

#include "swift/SILPasses/Utils/Local.h"
#include "swift/SILPasses/PassManager.h"
#include "swift/SIL/SILValue.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SIL/SILArgument.h"
#include "swift/SIL/SILFunction.h"
#include "swift/SIL/SILModule.h"
#include "swift/SILAnalysis/SpecializationsAnalysis.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

using namespace swift;

unsigned SpecializationsInfo::FunctionInfo::getSize() {
  // TODO: What happens if the body of the function was changed in the meantime?
  if (Size >= 0)
    return Size;
  auto *F = getFunction();
  unsigned size = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++size;
  Size = size;
  return size;
}

bool SpecializationsInfo::SpecializationInfo::isLayoutCompatibleWith(SpecializationInfo &RHS) {
  if (Layouts.size() != RHS.getLayouts().size())
    return false;

  for (int i = 0, e = Layouts.size(); i < e; ++i)
    if (Layouts[i].getEncoding() != RHS.getLayouts()[i].getEncoding())
      return false;

  return true;
}

void SpecializationsInfo::SpecializationInfo::computeLayouts() {
  for (auto Sub: Substitutions) {
    auto size = computeSymbolicLayout(Sub.getReplacement(), getModule());
    llvm::dbgs() << "Type " << Sub.getArchetype()->getName() << "=" << Sub.getReplacement() << " : " << size << "\n";
    llvm::dbgs() << "Layout encoding: " << size << "n";
    Layouts.push_back(size);
  }
  llvm::dbgs() << "\n";
}


// TODO: Should we use real references to SILFunctions instead of
// just names? Using real references would increase the reference
// count and thus prohibit them from removal by dead function
// elimination.
// Dead function elimination should remove a generic function,
// only if in addition to all usual conditions, it has no
// live specializations (which could be shared).

void SpecializationsInfo::verify() const {
  return;
  for (auto &Pair : Generic) {
    auto SpecName = Pair.getKey();
    auto GenericName = Pair.getValue();
    assert(Specializations.count(GenericName) && "There should be specializations for this generic");
    auto &Specs =  ((SpecializationsInfo*)this)->Specializations[GenericName];
    bool Found = false;
    for (auto &SI : Specs) {
      if (SI == SpecName) {
        Found = true;
        break;
      }
    }
    if (!Found) {
      llvm::dbgs() << "Specialization " << SpecName << " is not found in the specializations list of its generic\n";
      assert(Found);
    }
  }

  for (auto &Pair : Specializations) {
    auto GeneircName = Pair.getKey();
    auto Specs = Pair.getValue();
    for (auto &SI : Specs) {
      assert (Generic.count(SI) && "Unknown specialization in the list of specializations for a generic");
    }
  }
}

void SpecializationsInfo::verify(SILFunction *F) const {
  verify();
}

void SpecializationsInfo::registerSpecialization(SILFunction *OrigF,
                                        SILFunction *Specialization,
                               ArrayRef<Substitution> Substitutions) {
  auto OrigName = OrigF->getName();
  // TODO: Check that this specialization is not in the set of
  // specializations yet.
  for (auto S : Specializations[OrigName]) {
    assert(S != Specialization->getName() &&
           "Specialization is in the set already");
  }

  if (Specializations[OrigName].empty()) {
//    OrigF->incrementRefCount();
  }

  Specializations[OrigName].push_back(Specialization->getName());

  SpecInfo[Specialization->getName()] = SpecializationInfo(Specialization, Specialization->getName(), Substitutions);
  if (!GenericInfo.count(OrigName)) {
    GenericInfo[OrigName] = GenericFunctionInfo(OrigF, OrigName);
  }

  assert(!Generic.count(Specialization->getName()) &&
         "Specialization cannot have multiple generic parents");
  Generic[Specialization->getName()] = OrigName;
//  llvm::dbgs() << "Register specialization: " << Specialization->getName()
//               << "\n"
//               << "of generic function: " << OrigF->getName() << "\n";
//  OrigF->dump();
//  Specialization->dump();
}

void SpecializationsInfo::unregisterSpecialization(StringRef Name) {
    llvm::dbgs() << "Unregister specialization: " << Name << "\n";
    assert(Generic.count(Name) && "Specialization is not registered");
    auto GenericName = Generic[Name];
    auto &Specs =  Specializations[GenericName];
    assert(!Specs.empty() && "Specialization should be in the list");
    if (!Specs.empty()) {
      auto SizeBefore = Specs.size();
      Specs.erase(std::remove_if(Specs.begin(), Specs.end(),
                               [&Name](StringRef &SI)
                                 {return SI == Name;}));
      auto SizeAfter = Specs.size();
      assert(SizeAfter < SizeBefore && "Specialization should be removed from the list");
      if (Specs.empty()) {
        // No more live specializations are available.
        // If nothing else keeps this generic function alive, it can be
        // erased from the SIL module.
        llvm::dbgs() << "Unregister generic: " << GenericName << "\n";
        Specializations.erase(GenericName);
        GenericInfo.erase(GenericName);
        auto *GenericF = getModule()->lookUpFunction(GenericName);
//        GenericF->decrementRefCount();
      }
    }
    Generic.erase(Name);
    SpecInfo.erase(Name);
}

void SpecializationsInfo::unregisterSpecialization(SILFunction *F) {
  if (!Generic.count(F->getName()))
      return;
  unregisterSpecialization(F->getName());
}

void SpecializationsInfo::unregisterGeneric(StringRef Name) {
    llvm::dbgs() << "Unregister generic: " << Name << "\n";
    assert(Specializations.count(Name) && "Generic is not registered");
    auto &Specs =  Specializations[Name];
    assert(Specs.empty() && "No registered specializations should exist for this generic");
    Specializations.erase(Name);
    auto *GenericF = getModule()->lookUpFunction(Name);
//    GenericF->decrementRefCount();
}

void SpecializationsInfo::unregisterGeneric(SILFunction *F) {
  if (!Specializations.count(F->getName()))
      return;
  unregisterGeneric(F->getName());
}


/// Find a specialization of the function, which is compatible
/// with the given substitution.
SILFunction *SpecializationsInfo::findSpecialization(SILModule &M, SILFunction *F,
                               ArrayRef<Substitution> Substitutions) {
  return nullptr;
  llvm::dbgs() << "\n\nSearching an existing specialization for function: " << F->getName() << "\n";
  llvm::dbgs() << "With Substitutions:\n";
  for (auto Sub: Substitutions) {
    Sub.dump();
    llvm::dbgs() << "\n";
  }

  auto &GI = getGenericInfo(F);
  auto Kind = GI.getSpecializationSharingKind(*this);

#if 0
  // An experiment: only proceed if substitutions are either trivial types or classes.
  // For classes, we know the layout and we know how ARC operations are to be performed.
  // For trivial types we know their layout and size and we know that they do not need
  // any ARC operations.
  // Structures with both RC and non-RC payload require special handling and need to
  // invoke ARC operations via value witness tables. Apparently, many interesting
  // types fall into this category, e.g. String, Array, Dictionary.
  // In some cases, we could share, e.g. Array<Array<Int>> and Array<Array<UInt>>
  for (auto S: Substitutions) {
    auto R = S.getReplacement();
    auto LoweredTy = M.Types.getLoweredType(R);
    if (!LoweredTy.isTrivial(M) && !LoweredTy.isHeapObjectReferenceType()) {
      llvm::dbgs() << "Cannot find specialization: substitutions are not trivial and not heap objects: " << R <<"\n";
      return nullptr;
    }
  }
#endif

#if 0
  // If F is independent of size of generic parameters and
  // its specializations are not grouped according to any predicate,
  // then there is no need to specialize it at all.
  if (Kind == SpecializationSharingKind::LayoutIndependentSharing) {
    llvm::dbgs() << "Generic function is layout independent of its generic types: " << F->getName() << "\n";
    F->dump();
    auto Specs = SI.getSpecializations(F);
    if (Specs.empty())
      return nullptr;
    //return M.lookUpFunction(Specs[0]);
    return F;
  }
#endif

//  if (Kind == SpecializationSharingKind::LayoutDependentSharing ||
////      Kind == SpecializationSharingKind::LayoutIndependentSharing ||
//      Kind == SpecializationSharingKind::MetadataDependentSharing) {
  if (Kind >= SpecializationSharingKind::LayoutIndependentSharing &&
      Kind <= SpecializationSharingKind::LayoutDependentSharing) {
    llvm::dbgs() << "Generic function is layout dependent: " << F->getName() << "\n";
    // Find a specialization with matching layout.
    // TODO: Special handling for layouts that are:
    // - classes
    // - trivial types (i.e. pods) with a given layout (i.e. same size, alignment, etc).
    SpecializationsInfo::SpecializationInfo SpecInfoF(F, F->getName(), Substitutions);
    auto Specs = getSpecializations(F);
    for (auto &Spec: Specs) {
      llvm::dbgs() << "Checking against specialization: " << Spec << "\n";
      auto &SpecInfo = getSpecializationInfo(Spec);
      assert(SpecInfo.getLayouts().size() == SpecInfoF.getLayouts().size() &&
             "All specializations of the same function should have the same number of substitutions");
      for (int k = 0, ke = SpecInfo.getLayouts().size(); k < ke; ++k) {
        llvm::dbgs() << "\tLayout1: (" << SpecInfo.getLayouts()[k] << ") Layout2: (" << SpecInfoF.getLayouts()[k] << ")\n";
      }

      if (SpecInfo.isLayoutCompatibleWith(SpecInfoF))
        return M.lookUpFunction(Spec);
    }
  }

  // No matching specialization was found.
  return nullptr;
}

/// Checks if the size of the type \p Ty is size-dependent on any generic
/// parameters.
/// TODO: Use caching? Or even better make use of the structural dependency graph?
/// TODO: Does it need a GenTy parameter at all???
/// TODO: Structs/Tuples are actually passed by reference, if their size over a certain
///       threshold. Can we make use of it?
static bool isTypeSizeDependentOn(CanType Ty, CanType GenTy, SILModule &M) {
//  if (SILTy.isAddress())
//    return false;

  // If type is not generic in any form, it cannot be size dependent on
  // generic parameter types.
  if (!(Ty->hasTypeParameter() || Ty->hasArchetype() || Ty->isTypeParameter()))
    return false;

//  auto Ty = SILTy.getSwiftRValueType();
  // If type is a generic type, then the size of the value is certainly
  // dependent on the size of this type.
  if (Ty->isTypeParameter())
    return true;

  // If it is a reference counted type, its always allocated on heap
  // and the size of the reference is always of the same size.
  if (Ty.hasReferenceSemantics())
    return false;
//  if (SILType::getPrimitiveObjectType(Ty).isReferenceCounted(M))
//    return false;

  if (isa<MetatypeType>(Ty))
    return false;

  if (isa<ProtocolType>(Ty))
    return false;

  // If it is always a pointer size, then it is independent of generic type.
//  if (SILType::isPointerSizeAndAligned(Ty))
//    return false;

  // If it is a trivial type, it does not depend on the size of generic type.
  if (!Ty->hasTypeParameter() && SILType::getPrimitiveObjectType(Ty).isTrivial(M))
    return false;

  // Otherwise recurse into structural types.
  // If size of at least one of their fields is dependent on the size
  // of a generic type, then the size of the whole type is dependent on
  // the size of this generic type.
  if (auto *SD = Ty.getStructOrBoundGenericStruct()) {
      auto Range = SD->getStoredProperties();
      for (auto I = Range.begin(), E = Range.end();
             I != E; ++I) {
          Type FieldTy = (*I)->getType();
          if (FieldTy->isTypeParameter() || isa<ArchetypeType>(FieldTy.getCanonicalTypeOrNull()))
            return true;
          CanType EltTy = Ty->getTypeOfMember((*I)->getModuleContext(), *I, nullptr, (*I)->getInterfaceType()).getCanonicalTypeOrNull();
//          SILType EltTy = SILTy.getFieldType(*I, M);
//          CanType EltTy = FieldTy.getCanonicalTypeOrNull();
          //SILType EltTy = SILTy.getFieldType(*I, M);
          if (isTypeSizeDependentOn(EltTy, GenTy, M))
            return true;
        }
      return false;
    }

    if (auto *CD = Ty.getClassOrBoundGenericClass()) {
      auto Range = CD->getStoredProperties();
      for (auto I = Range.begin(), E = Range.end();
             I != E; ++I) {
          Type FieldTy = (*I)->getType();
          if (FieldTy->isTypeParameter() || isa<ArchetypeType>(FieldTy.getCanonicalTypeOrNull()))
            return true;
          CanType EltTy = Ty->getTypeOfMember((*I)->getModuleContext(), *I, nullptr, (*I)->getInterfaceType()).getCanonicalTypeOrNull();
//          SILType EltTy = SILTy.getFieldType(*I, M);
//          CanType EltTy = FieldTy.getCanonicalTypeOrNull();
          if (isTypeSizeDependentOn(EltTy, GenTy, M))
            return true;
        }
      return false;
    }

    if (auto *ED = Ty.getEnumOrBoundGenericEnum()) {
  //    CanTypeArrayRef GenericArgs;
  //    if (auto BGT = dyn_cast<BoundGenericType>(CanTy)) {
  //      GenericArgs = BGT.getGenericArgs();
  //    }
      /*
      auto Range = ED->getStoredProperties();
      for (auto I = Range.begin(), E = Range.end();
             I != E; ++I) {
          SILType EltTy = SILTy.getFieldType(*I, *M);
          addDependency(Deps, Id, EltTy);
        }
      */
        auto Range = ED->getAllElements();
        for (auto E: Range) {
            if (!E->hasArgumentType())
              continue;
            if (E->isIndirect())
              continue;
            CanType ArgType =
                Ty->getTypeOfMember(E->getModuleContext(), E,nullptr,
                    E->getArgumentInterfaceType()).getCanonicalTypeOrNull();
//            CanType ArgType = SILType::getPrimitiveObjectType(Ty).getEnumElementType(E, M).getSwiftRValueType();
//            CanType ArgType = E->getArgumentType().getCanonicalTypeOrNull();
//            SILType EltTy = SILType::getPrimitiveObjectType(ArgType);
            if (isTypeSizeDependentOn(ArgType, GenTy, M))
              return true;
          }
        return false;
    }

    if (auto TD = dyn_cast<TupleType>(Ty)) {
      auto Range = TD.getElementTypes();
      for (auto I = Range.begin(), E = Range.end();
             I != E; ++I) {
//          SILType EltTy = SILType::getPrimitiveObjectType(*I);
          if (isTypeSizeDependentOn((*I)->getCanonicalType(), GenTy, M))
            return true;
        }
      return false;
    }


  return true;
}

/// Figure if an existing implementation of a specialization can be reused
/// for a given apply.
/// This is usually possible if generic parameters are classes, because
/// classes are always passed by reference.
/// In case of structs, the situation is more difficult, because
/// the same implementation can be used only if structs are size/layout
/// compatible.
/// TODO: The property of being independent of the size of generic parameters
/// is a property of a function, not a property of the call. Therefore, it
/// should be lazily computed for functions and cached.
/// TODO: Group all specializations of a given function into categories:
/// - independent of of the size of generic parameters.
/// - dependent on the size of generic parameters (should be segregated by size)
/// - dependent on the refcount-ness of generic parameters (???)
SpecializationSharingKind
SpecializationsInfo::GenericFunctionInfo::getSpecializationSharingKind(SpecializationsInfo &SI) {
  if (Kind != Uninitialized)
    return Kind;

  SILFunction *F = getModule()->lookUpFunction(getFunctionName());
  Kind = LayoutIndependentSharing;
  auto LoweredFnTy = F->getLoweredFunctionType();
  auto Signature = LoweredFnTy->getGenericSignature();
  assert(Signature && "Function has no generic signature");

  llvm::dbgs() << "\nTrying to determine the specialization sharing kind of " << F->getName() << "\n";

  // If there are no requirements on the generic arguments, then only their
  // size/layout/alignment/representation and whether they are refcounted
  // may influence the decision of a specialization can be shared with
  // another specialization.

  // If none of the parameters and none of the instructions of function being
  // called depends on the size of generic parameter types, then such an
  // specialization can be shared with other specializations of the same
  // function, because the generated code would be the same.
  // NOTE: What about functions called/reachable from this function? What
  // if they are dependent on the size of generic parameters?

  // TODO: Even if there are requirements, but the code of the function
  // does not make use of them (i.e. it does not invoke any method
  // on the objects of a type involving a generic type, etc), then
  // it may still be OK to share such a specialization. Doing this
  // may require scanning the body of the function and eventually
  // scanning all functions reachable from it and taking any arguments
  // involving a constrained generic parameter with a requirement.

  auto Requirements = Signature->getRequirements();
  bool allowRequirements = true;

  // Are there any requirements demanding protocol conformances?
  bool hasRequirements = !(Requirements.size() == 1 &&
      Requirements[0].getKind() == RequirementKind::WitnessMarker);

  llvm::dbgs() << F->getName() << " has requirements:\n";
  Signature->dump();

  if (allowRequirements || !hasRequirements) {
    // There are no requirements.

    SILModule &M = F->getModule();

    if (Kind < LayoutDependentSharing) {
#if 0
      for (auto ParamTy : LoweredFnTy->getParameterSILTypes()) {
        if (isTypeSizeDependentOn(ParamTy.getSwiftRValueType(), CanType(), M)) {
          llvm::dbgs() << "\nSize of parameter type " << ParamTy
                       << " depends on size of generic type parameters\n";
          Kind = LayoutDependentSharing;
          break;
        }
      }
#else
      for (auto Param : LoweredFnTy->getParameters()) {
        // Indirect parameters are passed by reference.
        if (Param.isIndirect())
          continue;
        auto ParamTy = Param.getSILType();
        if (isTypeSizeDependentOn(ParamTy.getSwiftRValueType(), CanType(), M)) {
          llvm::dbgs() << "\nSize of parameter type " << ParamTy
                       << " depends on size of generic type parameters\n";
          Kind = LayoutDependentSharing;
          break;
        }
      }
#endif
    }

    if (F->isExternalDeclaration()) {
      // Typically, many functions from the runtime library fall into this category.
      // Handle them in a special way.
      llvm::dbgs() << "Cannot analyze the function because it has no body: " << F->getName() << "\n";
      // Assume the worst-case.
      if (hasRequirements) {
        Kind = RequirementsDependentSharing;
      } else {
        // As a test, do not assume the worst.
        // Kind = LayoutDependentSharing;
        if (F->getName().startswith("swift_")) {
          Kind = MetadataDependentSharing;
        }
      }
      llvm::dbgs() << "Sharing kind of " << F->getName() << " is: " << Kind << "\n";
      return Kind;
    }

    // Check all instructions of the function being specialized.
    // If any of them use a type whose size is dependent on the
    // size of generic parameter types, bail.
    // FIXME: This is a pretty expensive check as it traverses
    // all instructions!
    for (auto &BB : *F) {
      for (auto &I : BB) {

        // Only check invocations of functions, if there are any
        // requirements in the signature of the current generic function.
        // If there are no such requirements, there is no way for callees
        // to constrain the generic type and invoke any methods on it.
        // But callees my still try e.g. to get a size of the type.
        if (//hasRequirements &&
            Kind < RequirementsDependentSharing) {
          // Check all apply/try_apply/partial_apply instructions which
          // take arguments of types related to generic type arguments and
          // demand the type of the parameter to satisfy certain protocol
          // requirements. The callees should be checked recursively then.
          do {
            if (auto AI = ApplySite::isa(&I)) {
              bool usesGenericTypes = false;
              auto Subs = AI.getSubstitutions();
              // If the callee is not generic, bail.
              if (Subs.empty())
                break;

              llvm::dbgs() << "\nAnalyzing the apply site:\n";
              AI.getInstruction()->dumpInContext();
              // If none of substitutions are using any of generic types
              // from F's signature, bail.
              for (auto S : Subs) {
                auto Repl = S.getReplacement();
                // TODO: Is it enough as a test?
                if (Repl->hasUnboundGenericType() ||
                    Repl->hasArchetype() ||
                    Repl->hasTypeParameter()) {
                  // TODO: Check if this generic type is constrained in the
                  // signature of F.
                  usesGenericTypes = true;
                  break;
                }
              }

              if (!usesGenericTypes) {
                llvm::dbgs() << "Apply does not use any generic types\n";
                break;
              }

              llvm::dbgs() << "Checking the callee inside " << F->getName() << "\n";
              AI.getInstruction()->dump();

              // So, this call is using arguments of generic types having conformances.
              // We need to check the sharing kind of this callee.
              // TODO: Use a call graph here to get a list of callees for this call-site.
              // TODO: What if we have a circular dependency, i.e. the callee invokes F?
              //       May be we need to mark visited functions?
              auto Callee = AI.getCallee();
              auto *FRI = dyn_cast<FunctionRefInst>(Callee);
              if (!FRI) {
                llvm::dbgs() << "Callee is not a function_ref. Cannot analyze it.";
                //assert(FRI && "Callee is not a function_ref");
                break;
              }
              auto CalleeInfo = SI.getGenericInfo(FRI->getReferencedFunction());
              auto CalleeSharingKind = CalleeInfo.getSpecializationSharingKind(SI);
              if (Kind < CalleeSharingKind) {
                llvm::dbgs() << "Callee had a more constrained sharing kind";
                Kind = CalleeSharingKind;
              }
            }
          } while (false);

          // Check if this is a call of a method made stemming from a generic
          // type requirement, e.g. from a protocol requirement.
          if (auto *WMI = dyn_cast<WitnessMethodInst>(&I)) {
            // If there is only a dynamic dispatch involved, then calling
            // this method does not involve inlining anyways. So, it
            // should not be considered a problem for other optimizations.
            if (!WMI->isVolatile()) {
              auto Ty = WMI->getLookupType();
              if (auto AT = dyn_cast<ArchetypeType>(Ty)) {
                // TODO: Check that this archetype corresponds to one of the
                // generic type parameters in the function signature.
                Kind = RequirementsDependentSharing;
                llvm::dbgs()
                    << "\nA method from the requirement is being invoked:";
                WMI->dump();
              }
              if (Ty->isTypeParameter()) {
                Kind = RequirementsDependentSharing;
                llvm::dbgs()
                    << "\nA method from the requirement is being invoked:";
                WMI->dump();
              }
            }
          }
        }

#if 1
        if (Kind < LayoutDependentSharing) {
          auto ResultTypes = I.getTypes();
          for (unsigned i = 0, e = I.getNumTypes(); i < e; ++i) {
            auto Ty = I.getType(i);
            // Address never depends on the size.
            if (Ty.isAddress())
              continue;
            if (isTypeSizeDependentOn(Ty.getSwiftRValueType(),
                CanType(), M)) {
              llvm::dbgs()
                  << "\nInstruction depends on size of generic type parameters:\n";
              I.dumpInContext();
              Kind = LayoutDependentSharing;
              break;
            }
          }
        }

        if (Kind < LayoutDependentSharing) {
          auto Ops = I.getAllOperands();
          for (auto &Op : Ops) {
            bool IsDependent = false;
            auto Ty = Op.get().getType();
            // FIXME: Address never depends on size,
            // but some instructions taking address arguments do,
            // e.g. struct_element_addr

            // Any instruction that needs offset into a type that is
            // layout-dependent on a generic parameter,
            // is also layout dependent.
            if (isa<RefElementAddrInst>(&I) ||
                isa<StructElementAddrInst>(&I) ||
                isa<TupleElementAddrInst>(&I)) {
              if (isTypeSizeDependentOn(Ty.getSwiftRValueType(),
                  CanType(), M)) {
                IsDependent = true;
              }
            }

            // Address never depends on the size.
            if (!IsDependent && Ty.isAddress())
              continue;

            if (IsDependent || isTypeSizeDependentOn(Ty.getSwiftRValueType(),
                CanType(), M)) {
              llvm::dbgs()
                  << "\nInstruction depends on size of generic type parameters:\n";
              I.dumpInContext();
              Kind = LayoutDependentSharing;
              break;
            }
          }
        }

        // Check if metatype of a generic parameter (or a type dependent on a generic parameter)
        // is used by an instruction (e.g. many builtins like sizeof and alignof are using it)
        if (Kind < MetadataDependentSharing) {
          auto Ops = I.getAllOperands();
          for (auto &Op : Ops) {
            auto Ty = Op.get().getType();
            // Address never depends on the size.
            if (Ty.isAddress())
              continue;
            auto SwiftTy = Ty.getSwiftRValueType();
            if (!(SwiftTy->hasArchetype() || SwiftTy->hasTypeParameter() ||
                SwiftTy->hasUnboundGenericType()))
              continue;

            auto *BI = dyn_cast<BuiltinInst>(&I);
            if (!BI)
              continue;

            // Do we want to introduce a new sharing kind for functions having such instructions?
            switch (BI->getBuiltinInfo().ID) {
            case BuiltinValueKind::Sizeof:
            case BuiltinValueKind::Strideof:
            case BuiltinValueKind::StrideofNonZero:
            case BuiltinValueKind::Alignof:
            case BuiltinValueKind::CanBeObjCClass:
              break;
            default:
              continue;
            }

            llvm::dbgs()
                << "\nInstruction depends on metdata of generic type parameters:\n";
            I.dumpInContext();
//            Kind = LayoutDependentSharing;
            Kind = MetadataDependentSharing;
            break;
          }
        }
#endif
        if (Kind == NoSharing) {
          llvm::dbgs() << "Sharing kind of " << F->getName() << " is: " << Kind << "\n";
          return Kind;
        }
      }
    }

    llvm::dbgs() << "Sharing kind of " << F->getName() << " is: " << Kind << "\n";
    return Kind;
  }

  llvm::dbgs() << "\nGeneric parameters have requirements\n";
  Kind = RequirementsDependentSharing;
  llvm::dbgs() << "Sharing kind of " << F->getName() << " is: " << Kind << "\n";
  return Kind;
}


// Should we use the abstraction of a type instead?
// I.e. each builtin type is a unique SymbolicLayout object.
// Each compound type is a compound SymbolicLayout object.
// Each unique SymbolicLayout object represents a unique
// size, alignment and padding.

class BuiltinSymbolicLayout {
  int builtin: 1;
  unsigned size: 16;
  // Alignment. It is not a real alignment in bytes.
  // It is just a value representing a unique alignment of
  // a given builtin type. Two types with different alignment
  // are incompatible.
  unsigned alignment: 8;

public:
  // Types whose layout is known.
  static const BuiltinSymbolicLayout ObjectReference;
  static const BuiltinSymbolicLayout ClassReference;
  static const BuiltinSymbolicLayout FunctionReference;
  static const BuiltinSymbolicLayout WitnessTableReference;
  static const BuiltinSymbolicLayout IndirectEnumReference;
  static const BuiltinSymbolicLayout Generic;
  static const BuiltinSymbolicLayout Empty;

  // Basic types whose layout is known.
  static const BuiltinSymbolicLayout Int32;
  static const BuiltinSymbolicLayout Int64;
  static const BuiltinSymbolicLayout Int16;
  static const BuiltinSymbolicLayout Int8;
  static const BuiltinSymbolicLayout Int1;
  static const BuiltinSymbolicLayout Float;
  static const BuiltinSymbolicLayout Float80;
  static const BuiltinSymbolicLayout Double;
  static const BuiltinSymbolicLayout Word;

  BuiltinSymbolicLayout(unsigned size, unsigned alignment = 1):
    builtin(1), size(size), alignment(alignment) {
  }

  unsigned getAlignment() const {
    return alignment;
  }

  unsigned getSize() const {
    if (isBuiltin())
      return size;
    return 0;
  }

  bool isBuiltin() const {
    return builtin;
  }
};

/// A helper class for creation of
/// of a symbolic layout representation.
/// TODO: Preserve brackets?
/// Brackets with only one element inside (simple or compound) can be removed, because
/// the alignment of the struct with one element is the same as the alignment of this
/// element.
class SymbolicLayoutStream {
  llvm::SmallString<128> Buf;
  llvm::raw_svector_ostream Layout;
public:
  SymbolicLayoutStream() : Layout(Buf) {}

  /// Begin encoding a compound type.
  SymbolicLayoutStream& begin(Type Ty) {
    // Layout << "(";
    return *this;
  }

  /// End encoding a compound type.
  SymbolicLayoutStream& end(Type Ty) {
    // Layout << ")";
    return *this;
  }

  /// Add encoding of a known builtin type.
  SymbolicLayoutStream& operator << (const BuiltinSymbolicLayout &size) {
    Layout << "s" << size.getSize() << "a" << size.getAlignment();
    return *this;
  }

  /// Add encoding for a type with a known symbolic layout.
  SymbolicLayoutStream& operator << (SymbolicLayout &size) {
     Layout << size.getCanonicalEncoding();
     return *this;
  }

  SymbolicLayoutStream& operator << (StringRef str) {
     Layout << str;
     return *this;
  }

  SymbolicLayoutStream& operator << (size_t n) {
     Layout << n;
     return *this;
  }

  /// Get a symbolic layout of a type, whose representation
  /// was aggregated.
  SymbolicLayout getSymbolicLayout(SILModule *M) {
    // TODO: Produce a canonical encoding here?
    return SymbolicLayout(M->getASTContext().getIdentifier(Layout.str()).str());
  }
};

raw_ostream& swift::operator << (raw_ostream &stream, const SymbolicLayout &size) {
  stream << size.getCanonicalEncoding();
  return stream;
}

/// Check if two layout are compatible.
bool operator == (SymbolicLayout& lhs, SymbolicLayout &rhs) {
  return lhs.getCanonicalEncoding() == lhs.getCanonicalEncoding();
}

/// TODO: Add a more complicated logic here. It should get rid
/// of brackets in certain cases, etc.
StringRef swift::SymbolicLayout::getCanonicalEncoding() const {
  return getEncoding();
}

/// Static initializers.
const BuiltinSymbolicLayout BuiltinSymbolicLayout::ObjectReference(64, 1);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::FunctionReference(64, 2);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::ClassReference(64, 3);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::WitnessTableReference(64, 4);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::IndirectEnumReference(64, 5);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Generic(64, 6);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Empty(0, 7);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Int1(1, 8);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Int8(8, 9);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Int16(16, 10);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Int32(32, 11);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Int64(64, 12);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Float(32, 13);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Float80(80, 14);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Double(64, 15);
const BuiltinSymbolicLayout BuiltinSymbolicLayout::Word(32, 16);


/// Compute a size of a type in a symbolic form.

/// Builtin types have known size and alignment.

/// Two builtin types of the same size and with the same
/// alignment are considered the same.

/// Size of classes is always a constant, which is the size of a reference to a class.

/// Size of references to protocols with a given number of witness tables is constant, e.g.
/// all references to a protocol with a single witness table have the same size,
/// all references to a protocol protocol composition with N witness tables have the same size.

/// Size of an enum is the max of the size of its cases (now we have indirect enums and should be more careful)
/// For starters, it is probably easier to assume that each enum as a unique size.
/// Or that enums with only no-paylooad cases have the size of log2(number of cases) and enums with payload
/// cases have unique size (i.e. they are equivalent only to themselves).

/// Size of tuples is the sum of the sizes of its payload cases (alignment should be also taken into account)

/// Size of struct is the  sum of the sizes of its elements  (alignment should be also taken into account)

/// Size of compound types is computed recursively.

static void computeSymbolicLayoutInternal(Type Ty, SILModule *M, SymbolicLayoutStream &stream) {
  auto CanTy = Ty.getCanonicalTypeOrNull();

  // Metatypes are just references.
  if (isa<AnyMetatypeType>(CanTy)) {
    stream << BuiltinSymbolicLayout::ObjectReference;
    return;
  }

  if(isa<GenericTypeParamType>(CanTy)) {
    stream << BuiltinSymbolicLayout::Generic;
    return;
  }

  if (CanTy.getClassOrBoundGenericClass()) {
    stream << BuiltinSymbolicLayout::ObjectReference;
    return;
  }


  if (isa<AnyFunctionType>(CanTy)) {
    stream << BuiltinSymbolicLayout::FunctionReference;
    return;
  }

  if (isa<SILFunctionType>(CanTy)) {
    stream << BuiltinSymbolicLayout::FunctionReference;
    return;
  }

  if (isa<ReferenceStorageType>(CanTy)) {
    stream << BuiltinSymbolicLayout::ObjectReference;
    return;
  }

  ArrayRef<Substitution> Subs;
  if (auto BGT = dyn_cast<BoundGenericType>(CanTy)) {
    if (BGT->hasTypeParameter()) {
      stream << BuiltinSymbolicLayout::Generic;
      return;
    }
    Subs = BGT->getSubstitutions(nullptr, nullptr);
    if (hasUnboundGenericTypes(Subs)) {
      stream << BuiltinSymbolicLayout::Generic;
      return;
    }
  }

  // Existential types are represented as an object reference followed
  // by witness table references.
  if (CanTy.isAnyExistentialType() || isa<ProtocolCompositionType>(CanTy)) {
    SmallVector<ProtocolDecl *, 4> Protocols;
    CanTy.getAnyExistentialTypeProtocols(Protocols);
    if (!Protocols.empty()) {
      // This is an existential.
      // It's size is an object reference + witness_table references (1 per protocol).
      stream << BuiltinSymbolicLayout::ObjectReference;
      for (auto Protocol: Protocols)
        stream << BuiltinSymbolicLayout::WitnessTableReference;
    } else {
      // TODO: Do we need to output anything here?
    }
    return;
  }

  if (auto TD =  dyn_cast<TupleType>(CanTy)) {
    stream.begin(CanTy);
    for (auto Elt : TD->getElements()) {
      computeSymbolicLayoutInternal(Elt.getType(), M, stream);
    }
    if (!TD->getNumElements())
      stream << BuiltinSymbolicLayout::Empty;
    stream.end(CanTy);
    return;
  }

  if (auto *SD = CanTy.getStructOrBoundGenericStruct()) {
    // If struct has only one element, it is equivalent to the the element itself.
    auto Range = SD->getStoredProperties();

    auto NumElements = std::distance(Range.begin(), Range.end());
    if (NumElements == 1) {
      Type FieldTy = CanTy->getTypeOfMember(M->getSwiftModule(),
                                            *Range.begin(), nullptr);
      if (FieldTy->isTypeParameter() ||
          isa<ArchetypeType>(FieldTy.getCanonicalTypeOrNull()))
        assert(false &&
               "No properties of generic types should be found in the concrete struct type");
      computeSymbolicLayoutInternal(FieldTy.getCanonicalTypeOrNull(),
                                    M, stream);
      return;
    }

    stream.begin(CanTy);
    for (auto I = Range.begin(), E = Range.end(); I != E; ++I) {
      Type FieldTy = CanTy->getTypeOfMember(M->getSwiftModule(), *I, nullptr);
      if (FieldTy->isTypeParameter() ||
          isa<ArchetypeType>(FieldTy.getCanonicalTypeOrNull()))
        assert(false &&
               "No properties of generic types should be found in the concrete struct type");
      computeSymbolicLayoutInternal(FieldTy.getCanonicalTypeOrNull(),
                                    M, stream);
    }
    if (Range.empty()) {
      stream << BuiltinSymbolicLayout::Empty;
    }
    stream.end(CanTy);
    return;
  }

  if (auto *ED = CanTy.getEnumOrBoundGenericEnum()) {
    // TODO: Handle optionals in a special way.
    // Optional of heap referenced objects are
    // layout compatible with RawPointers.
    if (ED->isIndirect()) {
      stream << BuiltinSymbolicLayout::IndirectEnumReference;
      return;
    }

    if (M->getASTContext().getOptionalDecl() == ED) {
      // This is Optional.
      auto OptionalObjectType = CanTy.getAnyOptionalObjectType();
      if (OptionalObjectType &&
          SILType::getPrimitiveObjectType(OptionalObjectType).
                   isHeapObjectReferenceType()) {
        // Optional of a heap referenced type is layout compatible to
        // this reference type.
        computeSymbolicLayoutInternal(OptionalObjectType, M, stream);
        return;
      }
    }

    stream.begin(CanTy);
    auto Range = ED->getAllElements();
    SymbolicLayout *maxSize = nullptr;
    unsigned NumPayloadCases = 0;
    unsigned NumNoPayloadCases = 0;
    unsigned NumIndirectPayloadCases = 0;
    for (auto E : Range) {
      if (!E->hasArgumentType()) {
        NumNoPayloadCases++;
        continue;
      }
      if (E->isIndirect())
        NumIndirectPayloadCases++;
      else
        NumPayloadCases++;
    }


    // TODO: We need to distinguish between instantiations
    // of a generic enum with different generic parameters.
    // They are not equivalent to each other.
    if (NumPayloadCases + NumIndirectPayloadCases > 1) {
      // At SIL level, it is unknown how the layout of an enum with more
      // than one payload case would look like. Therefore, make this
      // enum equivalent only to itself.
      // TODO: Is this name is unique enough? Can we have two
      // different enums with the same name, but define in different
      // declaration contexts?
      // TODO: Should we use MD5? or just full name?
      size_t hash_code = size_t(llvm::hash_value(ED->getNameStr()));
      stream << "e" << hash_code;
      stream.end(CanTy);
      return;
    }

    // Push information about non-payload cases.
    stream << BuiltinSymbolicLayout(llvm::NextPowerOf2(NumPayloadCases), 1);

    // NOTE: Each enum with payload-cases is unique for now.
    stream.end(CanTy);
    return;
  }

  const SILType SILTy = SILType::getPrimitiveObjectType(CanTy);

  auto &Ctx = M->getASTContext();

  if (SILTy == SILType::getNativeObjectType(Ctx)) {
    stream << BuiltinSymbolicLayout::ObjectReference;
    return;
  }

  if (SILTy == SILType::getBridgeObjectType(Ctx)) {
    stream << BuiltinSymbolicLayout::ObjectReference;
    return;
  }

  if (SILTy == SILType::getRawPointerType(Ctx)) {
    stream << BuiltinSymbolicLayout::ObjectReference;
    return;
  }

  if (!SILTy.hasArchetype() && SILTy.isTrivial(*M)) {
    if (auto IT = dyn_cast<BuiltinIntegerType>(SILTy.getSwiftRValueType())) {
      if (IT->isFixedWidth()) {
        stream << BuiltinSymbolicLayout(IT->getFixedWidth(), 8);
        return;
      }
    }

    if (auto FT = dyn_cast<BuiltinFloatType>(SILTy.getSwiftRValueType())) {
        stream << BuiltinSymbolicLayout(FT->getBitWidth(), 13);
        return;
    }

    if (SILTy == SILType::getBuiltinWordType(Ctx)) {
      stream << BuiltinSymbolicLayout::Word;
      return;
    }

    if (auto VT = dyn_cast<BuiltinVectorType>(SILTy.getSwiftRValueType())) {
        stream.begin(VT.getPointer());
        stream << "v" << VT->getNumElements();
        computeSymbolicLayoutInternal(VT->getElementType(), M, stream);
        stream.end(VT.getPointer());
        return;
    }
  }

  llvm::dbgs() << "Cannot compute size of an unknown type:\n";
  CanTy.dump();
  llvm_unreachable("Unknown type");
  stream << BuiltinSymbolicLayout::ClassReference;
}

SymbolicLayout swift::computeSymbolicLayout(Type Ty, SILModule *M) {
  auto CanTy = Ty.getCanonicalTypeOrNull();

  // This is a top-level call.
  SymbolicLayoutStream Stream;
  computeSymbolicLayoutInternal(Ty, M, Stream);
  return Stream.getSymbolicLayout(M);
}


SILAnalysis *swift::createSpecializationsAnalysis(SILModule *M) {
  return new SpecializationsAnalysis(M);
}
