package esmeta.injector

import esmeta.state.*

/** assertions for conformance tests */
enum Assertion:
  case SameValue(exprSource: String, expected: SimpleValue)
  case CompareArray(exprSource: String, elements: Vector[ExpectedValue])
  case VerifyProperty(objSource: String, property: String)

/** expected value that can be asserted in generated tests */
enum ExpectedValue:
  case Simple(value: SimpleValue)
  case Array(elements: Vector[ExpectedValue])
