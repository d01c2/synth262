package esmeta.solver

import esmeta.util.BaseUtils.*
import esmeta.util.Appender.*
import esmeta.util.Appender.{*, given}

// symbolic environment mapping symbols to their shapes
case class SymEnv(map: Map[Symbol, Shape]) {
  // over-approximation of satisfiability checker
  def isBottom: Boolean = map.exists(_._2.isBottom)

  // precise satisfiability checker
  def check: Boolean = Solver.check(this)

  // get the shape of a symbolic expression under the symbolic environment
  def apply(sexpr: SymExpr): Shape = sexpr match
    case s: Symbol                   => map.getOrElse(s, Shape.Top)
    case SValue(ty)                  => Shape(ty)
    case SField(base, key)           => ???
    case SNot(base)                  => ???
    case SAnd(left, right)           => ???
    case SOr(left, right)            => ???
    case SImply(premise, conclusion) => ???
    case SEq(left, right)            => ???
    case SEqual(left, right)         => ???
    case SLt(left, right)            => ???
    case SExists(base, key)          => ???
    case STypeCheck(base, ty)        => ???
    case SOp(op, args)               => ???

  // refine the symbolic environment by adding a new shape for a symbol
  def refine(sym: Symbol, shape: Shape, pos: Boolean = true): SymEnv = SymEnv(
    map + (sym -> map.get(sym).fold(shape) { x =>
      if (pos) x && shape
      else x -- shape
    }),
  )

  // update
  def ++(pairs: Iterable[(Symbol, Shape)]): SymEnv = SymEnv(map ++ pairs)
  inline def ++(pairs: (Symbol, Shape)*): SymEnv = this ++ pairs

  override def toString: String = stringify(this)
}
object SymEnv {
  val empty: SymEnv = SymEnv(Map.empty)
  def apply(pairs: Iterable[(Symbol, Shape)]): SymEnv = SymEnv(pairs.toMap)
  inline def apply(pairs: (Symbol, Shape)*): SymEnv = SymEnv(pairs)
}

// stringify a symbolic environment
given symEnvRule: Rule[SymEnv] = (app, symEnv) => {
  given Rule[Map[Symbol, Shape]] = sortedMapRule(sep = ": ")
  app >> symEnv.map
}
