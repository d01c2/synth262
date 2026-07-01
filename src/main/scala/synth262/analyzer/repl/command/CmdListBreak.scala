package synth262.analyzer.repl.command

import synth262.analyzer.*
import synth262.analyzer.repl.*

trait CmdListBreakDecl { self: Self =>

// list-break command
  case object CmdListBreak
    extends Command(
      "list-break",
      "Show the list of break points.",
    ) {
    // options
    val options: List[String] = Nil

    // run command
    def apply(
      cpOpt: Option[ControlPoint],
      args: List[String],
    ): Unit = for {
      ((k, v), i) <- Repl.breakpoints.zipWithIndex
    } println(f"$i: $k%-15s $v")
  }
}
