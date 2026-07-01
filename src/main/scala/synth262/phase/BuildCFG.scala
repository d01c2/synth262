package synth262.phase

import synth262.*
import synth262.cfg.CFG
import synth262.cfgBuilder.CFGBuilder
import synth262.ir.Program
import synth262.util.*
import synth262.util.BaseUtils.*
import synth262.util.SystemUtils.*

/** `build-cfg` phase */
case object BuildCFG extends Phase[Program, CFG] {
  val name = "build-cfg"
  val help = "builds a control-flow graph (CFG) from an IR program."
  def apply(
    program: Program,
    cmdConfig: CommandConfig,
    config: Config,
  ): CFG = {
    // build cfg
    val builder = new CFGBuilder(program, config.log)
    val cfg = builder.result

    // logging mode
    if (config.log) cfg.dumpTo(CFG_LOG_DIR)

    // print DOT files
    if (config.dot)
      val dotDir = s"$CFG_LOG_DIR/dot"
      if (config.pdf && !isNormalExit("dot -V"))
        warn("- Graphviz `dot` is not installed!")
        warn("  (https://graphviz.org/doc/info/lang.html)")
        warn("- The `-build-cfg:pdf` option is turned off.")
        config.pdf = false
      cfg.dumpDot(dotDir, config.pdf)

    cfg
  }
  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "log",
      BoolOption(_.log = _),
      "turn on logging mode.",
    ),
    (
      "dot",
      BoolOption(_.dot = _),
      "dump the cfg in a DOT format.",
    ),
    (
      "pdf",
      BoolOption((c, b) => { c.dot ||= b; c.pdf = b }),
      "dump the cfg in DOT and PDF formats.",
    ),
  )
  case class Config(
    var log: Boolean = false,
    var dot: Boolean = false,
    var pdf: Boolean = false,
  )
}
