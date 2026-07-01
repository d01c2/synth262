package synth262.analyzer.repl.command

import synth262.analyzer.*
import synth262.analyzer.repl.*

trait CmdWorklistDecl { self: Self =>

// worklist command
  case object CmdWorklist
    extends Command(
      "worklist",
      "Show all the control points in the worklist",
    ) {
    // options
    val options @ List(detail) = List("detail")

    // run command
    def apply(
      cpOpt: Option[ControlPoint],
      args: List[String],
    ): Unit = {
      val size = worklist.size
      println(s"Total $size elements exist in the worklist.")
      args match {
        case s"-${`detail`}" :: _ => worklist.foreach(println(_))
        case _                    =>
      }
    }
  }
}
