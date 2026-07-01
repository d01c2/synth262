package synth262.phase

import synth262.*
import synth262.cfg.CFG
import synth262.util.*
import synth262.util.SystemUtils.*
import synth262.web.http.WebServer
import cats.effect.unsafe.implicits.global

/** `web` phase */
case object Web extends Phase[CFG, Unit] {
  val name = "web"
  val help = "starts a web server for an ECMAScript double debugger."
  def apply(
    cfg: CFG,
    cmdConfig: CommandConfig,
    config: Config,
  ): Unit =
    WebServer(cfg, config.host, config.port).run.unsafeRunSync()

  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "host",
      StrOption((c, s) => c.host = s),
      "web server host (default: env variable SYNTH262_HOST, localhost as fallback)",
    ),
    (
      "port",
      NumOption((c, i) => c.port = i),
      "web server port (default: 8080).",
    ),
  )
  case class Config(
    var host: String = sys.env.getOrElse("SYNTH262_HOST", "localhost"),
    var port: Int = 8080,
  )
}
