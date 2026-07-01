package synth262.extractor

import synth262.spec.Summary
import synth262.util.BaseUtils.*
import synth262.util.SystemUtils.*
import synth262.{Synth262Test, RESULT_DIR}

/** extractor validity test */
class ValiditySmallTest extends ExtractorTest {
  val name: String = "extractorValidityTest"

  // registration
  def init: Unit = {
    lazy val cur = Synth262Test.spec.summary
    check("extraction") { cur }
    val path = s"$RESULT_DIR/spec-summary"
    val prev = optional(Summary.fromFile(path)).getOrElse(cur)
    check("git version") { assert(prev.version == cur.version) }
    check("grammar") { assert(prev.grammar == cur.grammar) }
    check("algorithms") { assert(prev.algos.complete <= cur.algos.complete) }
    check("steps") { assert(prev.steps.complete <= cur.steps.complete) }
    check("types") { assert(prev.types.known <= cur.types.known) }
    check("tables") { assert(prev.tables == cur.tables) }
    check("type model") { assert(prev.tyModel == cur.tyModel) }
    dumpFile(cur, path)
  }

  init
}
