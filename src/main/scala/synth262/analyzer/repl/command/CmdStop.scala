package synth262.analyzer.repl.command

import synth262.analyzer.*
import synth262.analyzer.repl.*
import synth262.util.BaseUtils.*

trait CmdStopDecl { self: Self =>

// stop command
  case object CmdStop
    extends Command(
      "stop",
      "Stop the repl.",
    ) {
    // options
    val options = Nil

    // run command
    def apply(
      cpOpt: Option[ControlPoint],
      args: List[String],
    ): Unit = Repl.stop
  }
}
