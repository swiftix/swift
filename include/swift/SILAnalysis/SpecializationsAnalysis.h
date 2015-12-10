//===--_- Specializations.h - Analysis of the Call Graph -_-----*- C++ -*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SILANALYSIS_SPECIALIZATIONSANALYSIS_H
#define SWIFT_SILANALYSIS_SPECIALIZATIONSANALYSIS_H

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringMap.h"
#include "swift/SILAnalysis/Analysis.h"
#include "swift/SILPasses/Utils/Generics.h"

using namespace swift;

namespace swift {

class SILFunction;
class SILModule;

/// SymbolicLayout represents information about the layout
/// of a type (e.g. size of its elements, their alignment,
/// padding, etc) using a symbolic form.
/// Two types are considered layout compatible, if canonical
/// forms of their symbolic layouts are equal.
class SymbolicLayout {
  // Encoding of this symbolic size.
  StringRef Encoding;
public:
  SymbolicLayout(StringRef Enc): Encoding(Enc) {

  }

  StringRef getEncoding() const {
    return Encoding;
  }

  StringRef getCanonicalEncoding() const;
};

enum SpecializationSharingKind {
  Uninitialized,
  // Generic function does not depend on the layout of its generic parameters.
  // All specializations can be shared.
  LayoutIndependentSharing,
  // Generic function depends on the metadata of its generic parameters,
  // e.g. it uses sizeof or strideof.
  MetadataDependentSharing,
  // Generic function depends on the layout of its generic parameters.
  // Only specializations with layout-compatible generic parameters can be
  // shared.
  LayoutDependentSharing,
  // Generic function depends on the requirements of its generic parameters.
  RequirementsDependentSharing,
  // Specializations of a generic function cannot be shared.
  NoSharing = RequirementsDependentSharing
};

/// Compute a layout of a type in a symbolic form.
SymbolicLayout computeSymbolicLayout(Type Ty, SILModule *M);

raw_ostream& operator << (raw_ostream &stream, const SymbolicLayout &size);

class SpecializationsInfo {
public:

  class FunctionInfo {
    /// Name of the function.
    StringRef FunctionName;
    SILModule *M;
    int Size;
  public:
    FunctionInfo(SILFunction *F, StringRef Name):
      FunctionName(Name), M(&F->getModule()), Size(-1) {}
    FunctionInfo(): FunctionName(StringRef()), M(nullptr), Size(-1) {}

    unsigned getSize();

    SILModule *getModule() const {
      return M;
    }


    StringRef getFunctionName() const {
      return FunctionName;
    }

    SILFunction *getFunction() const {
      assert(M && "SILModule is not set");
      return M->lookUpFunction(getFunctionName());
    }

  };

  class GenericFunctionInfo: public FunctionInfo {
    SpecializationSharingKind Kind;
  public:
    GenericFunctionInfo() : FunctionInfo(), Kind(Uninitialized) {}

    GenericFunctionInfo(SILFunction *F, StringRef Name)
      : FunctionInfo(F, Name), Kind(Uninitialized) {}

    /// Checks if the code of a given function is dependent on the layout of
    /// its generic type parameters.
    SpecializationSharingKind getSpecializationSharingKind(SpecializationsInfo &SI);
  };

  class SpecializationInfo: public FunctionInfo {
    /// Substitutions used to generate this specialization.
    ArrayRef<Substitution> Substitutions;
    SmallVector<SymbolicLayout, 4> Layouts;

    void computeLayouts();
  public:
    SpecializationInfo() : FunctionInfo(), Substitutions({}) {}

    SpecializationInfo(SILFunction *F, StringRef Name, ArrayRef<Substitution> Subs)
      : FunctionInfo(F, Name), Substitutions(Subs) {
      computeLayouts();
    }

    ArrayRef<Substitution> getSubstitutions() const {
      return Substitutions;
    }

   ArrayRef<SymbolicLayout> getLayouts() {
     return Layouts;
   }

//   SmallVectorImpl<SymbolicLayout> &getLayouts() {
//     return Layouts;
//   }

   bool isLayoutCompatibleWith(SpecializationInfo &RHS);

  };

  typedef llvm::SmallVector<StringRef, 4> SpecializationsList;

private:
  SILModule *M;

  /// Maps a generic function with a given name to the
  /// set of its specializations.
  llvm::StringMap<SpecializationsList> Specializations;

  /// Maps a specialization with a given name to the
  /// generic function it was produced from.
  llvm::StringMap<StringRef> Generic;

  /// Maps a specialization with a given name to the
  /// specialization info.
  llvm::StringMap<SpecializationInfo> SpecInfo;

  /// Maps a generic function with a given name to the
  /// info about this function.
  llvm::StringMap<GenericFunctionInfo> GenericInfo;

public:
  SpecializationsInfo(SILModule *MM) : M(MM) {}

  /// Register a new specialization:
  /// - Remember what was the original non-specialized function
  /// - Add this specialization to the set of specializations of
  ///   the original non-specialized function.
  /// - Remember which substitutions were used to produce this
  ///   specialization.
  void registerSpecialization(SILFunction *OrigF,
                              SILFunction *Specialization,
                              ArrayRef<Substitution> Substitutions);

  void unregisterGeneric(StringRef Name);
  void unregisterGeneric(SILFunction *F);

  void unregisterSpecialization(StringRef Name);

  void unregisterSpecialization(SILFunction *F);

  SILModule *getModule() {
    return M;
  }

  ArrayRef<StringRef> getSpecializations(StringRef Name) {
    //return Specializations.lookup(Name);
    if (Specializations.count(Name))
      return Specializations[Name];
    return {};
//    return Specializations.lookup(Name);
  }

  ArrayRef<StringRef> getSpecializations(SILFunction *F) {
    return getSpecializations(F->getName());
  }

  StringRef getGenericFunction(StringRef Name) const {
    return Generic.lookup(Name);
  }

  StringRef getGenericFunction(SILFunction *F) const {
    return getGenericFunction(F->getName());
  }

  unsigned getSpecializedGenericsNum() const {
    return Specializations.size();
  }

  unsigned getSpecializationsNum() const  {
    return Generic.size();
  }

  SpecializationInfo &getSpecializationInfo(StringRef Name) {
    return SpecInfo[Name];
  }

  SpecializationInfo &getSpecializationInfo(SILFunction *F) {
    return getSpecializationInfo(F->getName());
  }

  GenericFunctionInfo &getGenericInfo(StringRef Name) {
    return GenericInfo[Name];
  }

  GenericFunctionInfo &getGenericInfo(SILFunction *F) {
    if (!GenericInfo.count(F->getName())) {
      GenericInfo[F->getName()] = GenericFunctionInfo(F, F->getName());
    }
    return getGenericInfo(F->getName());
  }


  const llvm::StringMap<SpecializationsList> &getSpeicalizedGenerics() const {
     return Specializations;
  }

  SILFunction *findSpecialization(SILModule &M, SILFunction *F,
                                 ArrayRef<Substitution> Substitutions);


  void verify() const;

  void verify(SILFunction *F) const;

};

/// The Call Graph Analysis provides information about the call graph.
class SpecializationsAnalysis : public SILAnalysis {
  SILModule *M;
  SpecializationsInfo *SI;

public:
  virtual ~SpecializationsAnalysis() {
  }

  SpecializationsAnalysis(SILModule *MM) : SILAnalysis(AnalysisKind::Specializations),
                                     M(MM), SI(nullptr) {}

  static bool classof(const SILAnalysis *S) {
    return S->getKind() == AnalysisKind::Specializations;
  }

  bool haveSpecializationsInfo() { return SI; }
  SpecializationsInfo *getSpecializationsInfoOrNull() { return SI; }
  SpecializationsInfo &getSpecializationsInfo() {
    assert(haveSpecializationsInfo() && "Expected constructed specialization info!");
    return *SI;
  }

  SpecializationsInfo &getOrBuildSpecializationsInfo() {
    if (!SI)
      SI = new SpecializationsInfo(M);
    return *SI;
  }

  virtual void invalidate(SILAnalysis::InvalidationKind K) {
    return;
  }

  virtual void invalidate(SILFunction *, SILAnalysis::InvalidationKind K) {
    invalidate(K);
  }

  virtual void verify() const {
#ifndef NDEBUG
    // If we don't have specializations information, return.
    if (!SI)
      return;
    SI->verify();
#endif
  }
  
  virtual void verify(SILFunction *F) const {
#ifndef NDEBUG
    // If we don't have specializations information, return.
    if (!SI)
      return;
    SI->verify(F);
#endif
  }
};

} // end namespace swift

#endif
