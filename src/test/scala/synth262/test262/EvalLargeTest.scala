package synth262.test262

import synth262.util.{ConcurrentPolicy => CP}

class EvalLargeTest extends Test262Test {
  val name: String = "test262EvalTest"

  // registration
  def init: Unit = check(name) {
    val (_, summary) = Test262Test.test262.evalTest(
      concurrent = CP.Auto,
      log = true,
      verbose = true,
    )
    val f = summary.failCount
    if (f > 0) fail(s"$f tests are failed.")
  }

  init
}
