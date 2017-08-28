
@_silgen_name("unknown")
public func unknown() -> ()

public func doSomething() {
  unknown()
}

@inline(never)
@_versioned
public func doSomething2() {
  unknown()
}

@inline(never)
@_versioned
public func doSomething3<T>(_ a:T) {
  unknown()
}

struct A {}
@inline(never)
public func callDoSomething3() {
  doSomething3(A())
}
