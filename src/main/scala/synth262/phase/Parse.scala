package synth262.phase

import synth262.*
import synth262.es.*
import synth262.parser.ESParser
import synth262.spec.Spec
import synth262.util.*
import synth262.util.SystemUtils.*

/** `parse` phase */
case object Parse extends Phase[Spec, Ast] {
  val name = "parse"
  val help = "parses an ECMAScript file."
  def apply(
    spec: Spec,
    cmdConfig: CommandConfig,
    config: Config,
  ): Ast =
    val filename = getFirstFilename(cmdConfig, name)
    ESParser(spec.grammar, config.debug)("Script").fromFile(filename)
  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "debug",
      BoolOption(_.debug = _),
      "turn on debugging mode.",
    ),
  )
  case class Config(
    var debug: Boolean = false,
  )
}
