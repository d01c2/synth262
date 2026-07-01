package synth262.compiler

import synth262.LINE_SEP
import synth262.util.BaseUtils.*
import synth262.util.SystemUtils.*
import synth262.{Synth262Test, RESULT_DIR}

/** compiler validity test */
class ValiditySmallTest extends CompilerTest {
  val name: String = "compilerValidityTest"

  // registration
  def init: Unit = {
    lazy val cur = Synth262Test.program.completeFuncs.map(_.name).toSet
    check("compilation") { cur }
    check("no unused manual rules") {
      val unusedRules = Synth262Test.compiler.unusedRules
      if (unusedRules.nonEmpty)
        fail(
          "there are unused manual rules:" + unusedRules.toList
            .map(rule => LINE_SEP + "* " + rule)
            .sorted
            .mkString,
        )
    }
    val path = s"$RESULT_DIR/complete-funcs"
    val prev = optional(readFile(path).split(LINE_SEP).toSet).getOrElse(cur)
    check("complete IR functions") { assert(prev subsetOf cur) }
    if (prev != cur) dumpFile(cur.toList.sorted.mkString(LINE_SEP), path)
  }

  init
}
