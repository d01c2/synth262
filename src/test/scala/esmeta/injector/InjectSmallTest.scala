package esmeta.injector

/** injection test */
class InjectSmallTest extends InjectorTest {
  val name: String = "injectorTest"

  def init: Unit = {
    val msg = "\"detailed description needed\""

    checkStringify("SameValue Assertion")(
      sameValueTest -> s"""
      |var __temp1 = 42 ;
      |assert.sameValue(__temp1, 42.0, $msg);
      |""".stripMargin.trim,
    )

    checkStringify("Throws Assertion")(
      throwsTest -> s"""
      |assert.throws(TypeError, function () {
      |  null . x ;
      |}, $msg);
      |""".stripMargin.trim,
    )

    checkStringify("CompareArray Assertion")(
      compareArrayTest -> s"""
      |var __temp1 = [ 1 , 2 , 3 ] ;
      |assert.compareArray(__temp1, [1.0, 2.0, 3.0], $msg);
      |""".stripMargin.trim,
    )
  }

  init
}
