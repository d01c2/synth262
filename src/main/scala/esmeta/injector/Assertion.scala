package esmeta.injector

import esmeta.state.*

/** assertions for conformance tests */
enum Assertion:
  case SameValue(variable: String, expected: SimpleValue)
  case CompareArray(variable: String, elements: Vector[ExpectedValue])

/** expected value */
enum ExpectedValue:
  case Simple(value: SimpleValue)
  case Array(elements: Vector[ExpectedValue])
