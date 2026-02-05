package esmeta.injector

import esmeta.state.*

/** assertions for conformance tests */
enum Assertion:
  case SameValue(expr: String, expected: SimpleValue)
  case CompareArray(expr: String, elements: Vector[ExpectedValue])
  case VerifyProperty(expr: String, property: String)

/** expected value */
enum ExpectedValue:
  case Simple(value: SimpleValue)
  case Array(elements: Vector[ExpectedValue])
