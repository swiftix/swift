//===--- TestsUtils.swift -------------------------------------------------===//
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

public protocol Proto {
  var xx: Int { set get }
  var yy: Int { set get }
  var zz: Int { set get }

  var aa: Int { set get }
  var bb: Int { set get }
}

@_fixed_layout
public struct ResilientFixedLayoutStruct: Proto, Hashable {
  public var x = 1
  public var y = 2
  public var z = 3

  private var a = 4

  public var xx: Int {
    get { return x }
    set { x = newValue }
  }
  public var yy: Int {
    get { return yy }
    set { yy = newValue }
  }
  public var zz: Int {
    get { return z }
    set { z = newValue }
  }

  public var aa: Int {
    get { return a }
    set { a = newValue }
  }

  public var bb: Int
}

public struct ResilientNonFixedLayoutStruct: Proto {
  public var x = 1
  public var y = 2
  public var z = 3

  private var a = 4

  public var xx: Int {
    get { return x }
    set { x = newValue }
  }
  public var yy: Int {
    get { return yy }
    set { yy = newValue }
  }
  public var zz: Int {
    get { return z }
    set { z = newValue }
  }

  public var aa: Int {
    get { return a }
    set { a = newValue }
  }

  public var bb: Int
}

