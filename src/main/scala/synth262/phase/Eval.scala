package synth262.phase

import synth262.*
import synth262.cfg.CFG
import synth262.interpreter.*
import synth262.ty.{*, given}
import synth262.ty.util.TypeErrorCollector
import synth262.state.*
import synth262.util.*
import synth262.util.SystemUtils.*

/** `eval` phase */
case object Eval extends Phase[CFG, State] {
  val name = "eval"
  val help = "evaluates an ECMAScript file."

  def apply(
    cfg: CFG,
    cmdConfig: CommandConfig,
    config: Config,
  ): State =
    val filename = getFirstFilename(cmdConfig, this.name)
    val st = run(cfg, config, filename)
    if (config.tyCheck)
      TypeErrorCollector(filename, st.typeErrors)
        .dumpTo(EVAL_LOG_DIR, withNames = false)
    st

  def run(cfg: CFG, config: Config, filename: String): State = Interpreter(
    cfg.init.fromFile(filename),
    tyCheck = config.tyCheck,
    log = config.log,
    detail = config.detail,
    timeLimit = config.timeLimit,
  )

  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "timeout",
      NumOption((c, k) => c.timeLimit = Some(k)),
      "set the time limit in seconds (default: no limit).",
    ),
    (
      "tycheck",
      BoolOption(_.tyCheck = _),
      "perform dynamic type checking.",
    ),
    (
      "log",
      BoolOption(_.log = _),
      "turn on logging mode.",
    ),
    (
      "detail-log",
      BoolOption((c, b) => { c.log ||= b; c.detail = b }),
      "turn on logging mode with detailed information.",
    ),
  )
  case class Config(
    var timeLimit: Option[Int] = None,
    var tyCheck: Boolean = false,
    var log: Boolean = false,
    var detail: Boolean = false,
  )
}
