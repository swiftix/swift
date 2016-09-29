//===----------------------------------------------------------------------===//
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

/// A COW (Copy-On-Write) protocol.
///
/// All COW types should conform to it.
/// The most prominent examples of such types in the standard library are:
/// Array, Dictionary, Set.

public protocol _COW {
}

public protocol COW : _COW {
}
