package esmeta.solver

import esmeta.cfg.Func
import esmeta.solver.SymInterp.State
import esmeta.spec.BuiltinHead
import esmeta.util.BaseUtils.*

object Reifier {

  /** reify a satisfiable path into an ECMAScript program */
  def apply(func: Func, state: State): Option[String] =
    val symEnv = state.symEnv
    val thisValue = symEnv(SThis)
    val rest = symEnv(SArgsList) // TODO : handle variadic parameters
    val newTarget = symEnv(SNewTarget)
    val len = func.head match {
      case Some(h: BuiltinHead) => h.arity._2
      case _                    => 0
    }
    val args = (0 until len).toList.map(i => symEnv(SArg(i)))
    for {
      path <- getPath(func)
      thisV <- thisValue.getJSExpr
      vs <- args.map(_.getJSExpr).sequence
    } yield reify(
      path,
      thisV,
      vs,
      if (Shape.Undef <= newTarget) None else newTarget.getJSExpr,
    )

  def getPath(func: Func): Option[String] = func.head match {
    case Some(h: BuiltinHead) => Some(h.path.toString)
    case _                    => None
  }

  def reify(
    path: String,
    thisValue: String,
    args: List[String],
    newTarget: Option[String],
  ): String = newTarget match
    case Some(nt) => ???
    case None     => s"$path.call($thisValue, ${args.mkString(", ")})"
}
