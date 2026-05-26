package esmeta.solver

import esmeta.ESMetaTest
import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*, Sym.*

/** test support for solver */
trait SolverTest extends ESMetaTest {
  def category: String = "solver"

  def solveAndReify(
    goal: Goal,
    params: List[Sym] = List(SolverTest.x),
  ): Option[Witness] =
    Solver.solve(goal).flatMap(Reify(_, params).witness)

  def checkUnsat(desc: String)(goal: Goal): Unit =
    check(desc)(assert(Solver.solve(goal).isEmpty))

  def checkWitness(desc: String, params: List[Sym] = List(SolverTest.x))(
    goal: Goal,
  )(assertion: Witness => Unit): Unit =
    check(desc) {
      solveAndReify(goal, params) match
        case Some(witness) => assertion(witness)
        case None          => fail(s"no witness for $desc")
    }

  def checkParamWitness(
    desc: String,
    param: Sym = SolverTest.x,
    params: List[Sym] = List(SolverTest.x),
  )(goal: Goal)(assertion: String => Unit): Unit =
    checkWitness(desc, params)(goal) { witness =>
      assertion(witness.getOrElse(param, fail(s"missing witness for $param")))
    }
}

object SolverTest {
  val x: Sym = Arg(0)
  val y: Sym = Arg(1)

  lazy val xSym: SymExpr = SESym(x)
  lazy val ySym: SymExpr = SESym(y)

  def isType(expr: SymExpr, ty: ValueTy): Formula =
    FEq(SETypeOf(expr), SEType(ty))

  def isValue(expr: SymExpr, lit: LiteralExpr): Formula =
    FEq(expr, SELit(lit))

  def isNotValue(expr: SymExpr, lit: LiteralExpr): Formula =
    FNot(isValue(expr, lit))

  def isNotType(expr: SymExpr, ty: ValueTy): Formula =
    FNot(isType(expr, ty))
}
