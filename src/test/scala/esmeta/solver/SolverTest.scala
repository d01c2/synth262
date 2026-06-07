package esmeta.solver

import esmeta.ESMetaTest
import esmeta.cfg.CFG
import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*, Sym.*

/** test support for solver */
trait SolverTest extends ESMetaTest {
  given CFG = CFG()
  protected val solver: Solver = Solver()
  def category: String = "solver"

  def solveAndReify(
    goal: List[Formula],
    params: List[Sym] = List(SolverTest.x),
  ): Option[Witness] =
    solver.solve(goal).flatMap(Reify(_, params).witness)

  def checkUnsat(desc: String)(goal: List[Formula]): Unit =
    check(desc)(assert(solver.solve(goal).isEmpty))

  def checkWitness(desc: String, params: List[Sym] = List(SolverTest.x))(
    goal: List[Formula],
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
  )(goal: List[Formula])(assertion: String => Unit): Unit =
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
    FTypeCheck(expr, ty)

  def isValue(expr: SymExpr, lit: LiteralExpr): Formula =
    FEq(expr, SELit(lit))

  def isNotValue(expr: SymExpr, lit: LiteralExpr): Formula =
    FNot(isValue(expr, lit))

  def isNotType(expr: SymExpr, ty: ValueTy): Formula =
    FNot(isType(expr, ty))
}
