package esmeta.injector

import esmeta.cfg.CFG
import esmeta.injector.util.*
import esmeta.util.BaseUtils.*

/** conformance test */
case class ConformTest(
  harness: String,
  script: String,
  exitTag: ExitTag,
  throwingExpr: Option[String],
) {
  import Stringifier.{*, given}
  override def toString: String = stringify(this)
}

object ConformTest {

  /** Create a test using a hooking interpreter */
  def createTest(cfg: CFG, interp: HookingInterpreter): ConformTest =
    val sourceText = interp.result.cachedSourceText.getOrElse("")
    new Injector(cfg, interp, "", sourceText, log = false).conformTest
}
