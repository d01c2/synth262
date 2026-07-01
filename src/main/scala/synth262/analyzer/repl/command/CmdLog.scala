package synth262.analyzer.repl.command

import synth262.analyzer.*
import synth262.analyzer.repl.*

trait CmdLogDecl { self: Self =>

// log command
  case object CmdLog
    extends Command(
      "log",
      "Dump the current analysis result.",
    ) {
    // options
    val options = Nil

    // run command
    def apply(
      cpOpt: Option[ControlPoint],
      args: List[String],
    ): Unit = logging
  }
}
