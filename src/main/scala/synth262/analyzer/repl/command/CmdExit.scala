package synth262.analyzer.repl.command

import synth262.analyzer.*
import synth262.analyzer.repl.*
import synth262.util.BaseUtils.*

trait CmdExitDecl { self: Self =>

// exit command
  case object CmdExit
    extends Command(
      "exit",
      "Exit the type checking.",
    ) {
    // options
    val options = Nil

    // run command
    def apply(
      cpOpt: Option[ControlPoint],
      args: List[String],
    ): Unit = raise("stop for debugging")
  }
}
