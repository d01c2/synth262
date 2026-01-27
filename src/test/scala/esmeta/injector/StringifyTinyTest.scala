package esmeta.injector

/** stringify test */
class StringifyTinyTest extends InjectorTest {
  val name: String = "injectorStringifyTest"

  def init: Unit = {
    val msg = "\"detailed description needed\""

    checkStringify("Normal Exit ConformTest")(
      normalExitTest -> s"""
      |var __temp1 = 42 ;
      |assert.sameValue(__temp1, 42.0, $msg);
      |""".stripMargin.trim,
    )

    checkStringify("Throw Exit ConformTest")(
      throwExitTest -> s"""
      |assert.throws(TypeError, function () {
      |  null . foo ;
      |}, $msg);
      |""".stripMargin.trim,
    )
  }

  init
}
