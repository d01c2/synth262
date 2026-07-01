package synth262.analyzer

import synth262.Synth262Test
import synth262.analyzer.tychecker.TyChecker
import synth262.analyzer.tychecker.TyChecker.Ignore
import synth262.cfg.CFG
import synth262.util.*

/** analyzer tests */
trait AnalyzerTest extends Synth262Test {
  def category: String = "analyzer"
}
object AnalyzerTest {
  import Synth262Test.*
  lazy val tychecker: TyChecker = getAnalyzer(cfg)
  inline def ignore: Ignore = ManualInfo.tycheckIgnore

  // helper methods
  def getAnalyzer(target: String): TyChecker = getAnalyzer(getCFG(target))
  def getAnalyzer(cfg: CFG): TyChecker = getAnalyzer(cfg, ignore)
  def getAnalyzer(cfg: CFG, ignore: Ignore): TyChecker = TyChecker(
    cfg = cfg,
    ignore = ignore,
    silent = true,
  )
}
