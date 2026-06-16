package esmeta.solver

import esmeta.ty.*
import esmeta.util.BaseUtils.*
import esmeta.util.Appender.*
import esmeta.util.Appender.{*, given}

object Solver {
  // add a formula to the current symbolic environment
  def add(symEnv: SymEnv, sexpr: SymExpr, side: Boolean): SymEnv = sexpr match
    case SArg(i)              => ???
    case SThis                => ???
    case SArgsList            => ???
    case SNewTarget           => ???
    case SGlobal(name)        => ???
    case SValue(ty)           => ???
    case SField(base, key)    => ???
    case SNot(base)           => ???
    case SAnd(left, right)    => ???
    case SOr(left, right)     => ???
    case SEq(x: Symbol, expr) => symEnv.refine(x, symEnv(expr), side)
    case SEq(left, right)     => ???
    case SEqual(left, right)  => ???
    case SLt(left, right)     => ???
    case SExists(base, key)   => ???
    case STypeCheck(base, ty) => ???
    case SOp(op, args)        => ???

  // check if the current symbolic environment is reifiable
  def check(symEnv: SymEnv): Boolean = !symEnv.isBottom // TODO: more precise
}
