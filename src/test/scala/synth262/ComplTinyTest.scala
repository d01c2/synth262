package synth262

import synth262.BASE_DIR
import synth262.util.GenCompl
import synth262.util.BaseUtils.*
import synth262.util.SystemUtils.*

/** test for .completion file */
class ComplTinyTest extends Synth262Test {
  def category: String = "general"
  val name: String = "complTest"

  // registration
  def init: Unit = {
    val expected = GenCompl.content
    val result = optional(readFile(s"$BASE_DIR/.completion")).getOrElse("")
    check("completion") {
      if (result != expected) GenCompl.update
      assert(result == expected)
    }
  }
  init
}
