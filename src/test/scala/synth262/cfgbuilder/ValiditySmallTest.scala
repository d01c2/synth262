package synth262.cfgBuilder

import synth262.Synth262Test

/** compiler validity test */
class ValiditySmallTest extends CFGBuilderTest {
  val name: String = "cfgBuilderValidityTest"

  // registration
  def init: Unit = {
    lazy val cfg = Synth262Test.cfg
    check("CFG build") { cfg }
  }

  init
}
