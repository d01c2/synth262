package esmeta.injector

/** injection test */
class InjectSmallTest extends InjectorTest {
  val name: String = "injectorTest"

  def init: Unit = {
    val msg = "\"detailed description needed\""

    checkStringify("SameValue Assertion")(
      sameValueTest -> s"""assert.sameValue(42 , 42.0, $msg);""",
    )

    checkStringify("Throws Assertion")(
      throwsTest -> s"""
      |assert.throws(TypeError, function () {
      |  null . x ;
      |}, $msg);
      |""".stripMargin.trim,
    )

    checkStringify("CompareArray Assertion")(
      compareArrayTest -> s"""assert.compareArray([ 1 , 2 , 3 ] , [1.0, 2.0, 3.0], $msg);""",
    )
  }

  init
}
