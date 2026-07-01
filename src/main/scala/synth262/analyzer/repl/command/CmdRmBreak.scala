package synth262.analyzer.repl.command

import synth262.analyzer.*
import synth262.analyzer.repl.*
import synth262.util.BaseUtils.*

trait CmdRmBreakDecl { self: Self =>

// rm-break command
  case object CmdRmBreak
    extends Command(
      "rm-break",
      "Remove a break point.",
    ) {
    // options
    val options @ List(all) = List("all")

    // run command
    def apply(
      cpOpt: Option[ControlPoint],
      args: List[String],
    ): Unit = args match {
      case Nil => println("need arguments")
      case arg :: _ => {
        val breakpoints = Repl.breakpoints
        optional(arg.toInt) match {
          case _ if arg == s"-$all" => breakpoints.clear
          case Some(idx) if idx.toInt < breakpoints.size =>
            breakpoints.remove(idx.toInt)
          case _ => println("Inappropriate argument")
        }
      }
    }
  }
}
