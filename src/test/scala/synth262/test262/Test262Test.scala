package synth262.test262

import synth262.*
import synth262.spec.Spec
import synth262.test262.*
import synth262.test262.util.*
import synth262.util.BaseUtils.*
import synth262.util.SystemUtils.*

trait Test262Test extends Synth262Test {
  def category: String = "test262"
}
object Test262Test {
  lazy val test262 = Test262(Test262.currentVersion, Synth262Test.cfg)
}
