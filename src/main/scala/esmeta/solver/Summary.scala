package esmeta.solver

import esmeta.ty.*

// summary for abstract operations
case class Summary(impls: List[Summary.Imply])

object Summary {
  // implication between return value of callee and must-true
  // condition for arguments of callee
  case class Imply(
    post: SymExpr, // return value of callee
    pre: SymEnv,  // must-true condition for arguments of callee
  )

  def apply(impls: Imply*): Summary = Summary(impls.toList)

  val manual: Map[String, Summary] = Map(
    /* TODO */
  )
}
