package synth262.analyzer.repl.command

import synth262.analyzer.*
import synth262.analyzer.util.*
import synth262.analyzer.repl.*
import synth262.util.BaseUtils.*
import synth262.util.SystemUtils.*

trait CmdGraphDecl { self: Self =>

// graph command
  case object CmdGraph
    extends Command(
      "graph",
      "Dump the current control graph.",
    ) {
    import DotPrinter.*

    // options
    val options @ List(total) = List("total")

    // run command
    def apply(
      cpOpt: Option[ControlPoint],
      args: List[String],
    ): Unit = (optional(args.head.toInt), args) match
      case (Some(depth), _) => dumpCFG(cpOpt, depth = Some(depth))
      case (None, s"-$total" :: _) =>
        dumpCFG(cpOpt, depth = None)
      case _ => dumpCFG(cpOpt, depth = Some(0))
  }
}
