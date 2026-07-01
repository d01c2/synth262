package synth262.es

import synth262.{Synth262Test, ES_TEST_DIR}
import synth262.analyzer.*
import synth262.util.SystemUtils.*

class AnalyzeSmallTest extends ESTest {
  import ESTest.*

  val name: String = "esAnalyzeTest"

  // registration
  def init: Unit =
    // TODO revert
    // for (file <- walkTree(ES_TEST_DIR)) {
    //   val filename = file.getName
    //   if (jsFilter(filename))
    //     check(filename) { analyzeTestFile(file.toString) }
    // }
    // init
    ()
}
