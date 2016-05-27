//===- SILOpenedArchetypeTracker.h - Track opened archetypes  ---*- C++ -*-===//
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

#ifndef SWIFT_SIL_SILOPENEDARCHETYPESTRACKER_H
#define SWIFT_SIL_SILOPENEDARCHETYPESTRACKER_H

#include "swift/SIL/Notifications.h"
#include "swift/SIL/SILModule.h"
#include "swift/SIL/SILFunction.h"
#include "swift/SIL/SILUndef.h"

namespace swift {

class SILOpenedArchetypesTracker;

/// Find an opened archetype defined by an instruction.
/// \returns The found archetype or empty type otherwise.
CanType getOpenedArchetypeOf(const SILInstruction *I);

/// Find an opened archetype represented by this type.
/// \returns The found archetype or empty type otherwise.
CanType getOpenedArchetypeOf(CanType Ty);

/// Return the defintion of an opened archetype.
/// It it is an opened archetype, but its definition is not known
/// yet, return a SILUndef with the type of this opened archetype
/// Otehrwise return a SILUndef of non-archetype type.
SILValue
getOpenedArchetypeDef(SILType SILTy, SILModule &M,
                      SILOpenedArchetypesTracker *OpenedArchetypes = nullptr);

/// SILOpenedArchetypesTracker is a helper class that can be used to create
/// and maintain a mapping from opened archetypes to instructions
/// defining them, e.g. open_existential_ref, open_existential_addr,
/// open_existential_metatype.
///
/// This information is useful for representing and maintaining the
/// dependencies of instructions on opened archetypes they are using.
class SILOpenedArchetypesTracker : public DeleteNotificationHandler {
public:
  typedef llvm::DenseMap<Type, SILValue> OpenedArchetypeDefsMap;
  // Re-use pre-populated map if available.
  SILOpenedArchetypesTracker(const SILFunction &F,
                             SILOpenedArchetypesTracker &Tracker)
      : F(F), OpenedArchetypeDefs(Tracker.OpenedArchetypeDefs) { }

  // Re-use pre-populated map if available.
  SILOpenedArchetypesTracker(const SILFunction &F,
                             OpenedArchetypeDefsMap &OpenedArchetypeDefs)
      : F(F), OpenedArchetypeDefs(OpenedArchetypeDefs) { }

  // Use its own local map if no pre-populated map is provided.
  SILOpenedArchetypesTracker(const SILFunction &F)
      : F(F), OpenedArchetypeDefs(LocalOpenedArchetypeDefs) { }


  const SILFunction &getFunction() { return F; }

  void addOpenedArchetypeDef(Type archetype, SILValue Def) {
    assert(!getOpenedArchetypeDef(archetype) &&
           "There can be only one definition of an opened archetype");
    OpenedArchetypeDefs[archetype] = Def;
  }

  void removeOpenedArchetypeDef(Type archetype, SILValue Def) {
    auto FoundDef = getOpenedArchetypeDef(archetype);
    assert(FoundDef &&
           "Opened archetype definition is not registered in SILFunction");
    if (FoundDef == Def)
      OpenedArchetypeDefs.erase(archetype);
  }

  // Return the SILValue defining a given archetype.
  // If the defining value is not known, return an empty SILValue.
  SILValue getOpenedArchetypeDef(Type archetype) const {
    return OpenedArchetypeDefs.lookup(archetype);
  }

  const OpenedArchetypeDefsMap &getOpenedArchetypeDefs() {
    return OpenedArchetypeDefs;
  }

  // Register archetypes opened by a given instruction.
  // Can be used to incrementally populate the mapping, e.g.
  // if it is done when performing a scan of all instructions
  // inside a function.
  void registerOpenedArchetypes(const SILInstruction *I);

  // Register opened archetypes whose definitions are referenced by
  // the typedef operands of this instruction.
  void registerUsedOpenedArchetypes(const SILInstruction *I);

  // Unregister archetypes opened by a given instruction.
  // Should be only called when this instruction is to be removed.
  void unregisterOpenedArchetypes(const SILInstruction *I);

  // Handling of instruction removal notifications.
  bool needsNotifications() { return true; }

  // Handle notifications about removals of instructions.
  void handleDeleteNotification(swift::ValueBase *Value);

  virtual ~SILOpenedArchetypesTracker() {
    // Unregister the handler.
    F.getModule().removeDeleteNotificationHandler(this);
  }

private:
  /// The function whose opened archetypes are being tracked.
  /// Used only for verification purposes.
  const SILFunction &F;
  /// Mapping from opened archetypes to their definitions.
  OpenedArchetypeDefsMap &OpenedArchetypeDefs;
  /// Local map to be used if no other map was provided in the
  /// constructor.
  OpenedArchetypeDefsMap LocalOpenedArchetypeDefs;
};

} // end swift namespace
#endif
