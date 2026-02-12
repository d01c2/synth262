package esmeta.phase

import esmeta.*
import esmeta.cfg.CFG
import esmeta.injector.Injector
import esmeta.es.*
import esmeta.state.*
import esmeta.util.*
import esmeta.util.SystemUtils.*

/** `inject` phase */
case object Inject extends Phase[CFG, String] {
  val name = "inject"
  val help = "injects assertions to check final state of an ECMAScript file."
  def apply(
    cfg: CFG,
    cmdConfig: CommandConfig,
    config: Config,
  ): String =
    val filename = getFirstFilename(cmdConfig, this.name)
    val src = readFile(filename)
    val test = Injector(cfg, src)
    val injected = test.toString

    // dump the assertion-injected ECMAScript program
    for (filename <- config.out)
      dumpFile(
        name = "an assertion-injected ECMAScript program",
        data = injected,
        filename = filename,
      )

    injected
  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "out",
      StrOption((c, s) => c.out = Some(s)),
      "dump an assertion-injected ECMAScript program to a given path.",
    ),
  )
  case class Config(
    var out: Option[String] = None,
  )
}
