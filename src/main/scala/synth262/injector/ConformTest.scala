package synth262.injector

import synth262.*
import synth262.cfg.CFG
import synth262.error.NoGraalError
import java.util.concurrent.TimeoutException
import synth262.es.*
import synth262.es.util.*
import synth262.state.State
import synth262.util.*
import synth262.util.SystemUtils.*
import scala.util.*

/** conformance test */
case class ConformTest(
  id: Int,
  script: String,
  exitTag: ExitTag,
  async: Boolean,
  assertions: Vector[Assertion],
) extends InjectorElem
  with UId

object ConformTest {

  /** Create a test using init state and exit state */
  def createTest(cfg: CFG, exitSt: State): ConformTest =
    new Injector(cfg, exitSt, false).conformTest
}
