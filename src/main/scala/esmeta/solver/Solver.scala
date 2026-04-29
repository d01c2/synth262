package esmeta.solver

import esmeta.ir.*
import esmeta.ty.*
import Formula.*, Term.*

type Goal = List[Formula]
type Witness = Map[String, String]

// Constraint solver
object Solver:
  def solve(goal: Goal, entryParams: List[String]): Option[Witness] =
    val entrySet = entryParams.toSet
    val eliminated = eliminate(goal, entrySet)
    simplify(eliminated).flatMap(Reify(_, entryParams).witness)

  // Eliminate non-entry variables occurring in conjunction of formulas
  private def eliminate(
    formulas: Goal,
    entryParams: Set[String],
  ): List[Formula] =
    val afterVars = inlineVar(formulas, entryParams)
    val afterFields = inlineFields(afterVars, entryParams)
    // If field inlining made progress, re-run variable inlining
    if (afterFields != afterVars) eliminate(afterFields, entryParams)
    else afterFields

  // Inline non-entry variables
  private def inlineVar(
    formulas: List[Formula],
    entryParams: Set[String],
  ): List[Formula] =
    val nonEntry = formulas.flatMap(_.freeVars).toSet -- entryParams
    formulas.zipWithIndex.collectFirst {
      // substitute x to t, where x is non-entry and does not occur in t
      case (FEq(TVar(x), t), i) if nonEntry(x) && !t.occurs(x) => (i, x, t)
      case (FEq(t, TVar(x)), i) if nonEntry(x) && !t.occurs(x) => (i, x, t)
    } match
      case Some((idx, name, rep)) =>
        // drop the equation used for substitution
        val updated =
          formulas.patch(idx, Nil, 1).map(_.rewrite(TVar(name), rep))
        inlineVar(updated, entryParams)
      case None => formulas

  // Inline field-access terms for non-entry variables
  private def inlineFields(
    formulas: List[Formula],
    entryParams: Set[String],
  ): List[Formula] =
    val nonEntry = formulas.flatMap(_.freeVars).toSet -- entryParams

    // non-entry variables occurring in field-access terms
    val fieldedVars = formulas.flatMap {
      case FEq(TField(TVar(x), _), _) if nonEntry(x) => Some(x)
      case FEq(_, TField(TVar(x), _)) if nonEntry(x) => Some(x)
      case _                                         => None
    }.distinct

    fieldedVars.foldLeft(formulas) { (fs, name) =>
      // partition field-access equations from the rest
      val (defs, rest) = fs.partition {
        case FEq(TField(TVar(x), _), _) if x == name => true
        case FEq(_, TField(TVar(x), _)) if x == name => true
        case _                                       => false
      }

      // build a map from field name to its bound term
      val bindings = defs
        .collect {
          case FEq(TField(TVar(_), k), v) => k -> v
          case FEq(v, TField(TVar(_), k)) => k -> v
        }
        .groupMap(_._1)(_._2)
        .map { case (k, vs) => k -> vs.head }

      // keep unresolved field equations
      val unresolved = defs.filterNot {
        case FEq(TField(_, k), _) => bindings.contains(k)
        case FEq(_, TField(_, k)) => bindings.contains(k)
        case _                    => false
      }

      // rewrite field references with resolved values
      bindings.foldLeft(rest ++ unresolved) {
        case (fs, (k, v)) =>
          fs.map(_.rewrite(TField(TVar(name), k), v))
      }
    }

  // Flatten double negations and normalize completion type negations
  private def flatten(f: Formula): Formula = f match
    case FNot(FNot(inner)) => flatten(inner)
    case FNot(FEq(TTypeOf(t), TType(ty))) if ty <= NormalT =>
      FEq(TTypeOf(t), TType(AbruptT))
    case FNot(FEq(TTypeOf(t), TType(ty))) if ty <= AbruptT =>
      FEq(TTypeOf(t), TType(NormalT))
    case FNot(inner) => FNot(flatten(inner))
    case _           => f

  // Remove tautologies and redundant constraints; detect contradictions
  private def simplify(fs: List[Formula]): Option[List[Formula]] =
    val flat = fs.map(flatten)
    val termToLit: Map[Term, LiteralExpr] = flat.collect {
      case FEq(t, TLit(v)) => t -> v
      case FEq(TLit(v), t) => t -> v
    }.toMap
    // contradiction: two different literals asserted equal, or
    // negation of a tautology (NOT (x == x))
    val hasContradiction = flat.exists {
      case FEq(TLit(a), TLit(b))     => a != b
      case FEq(t, TLit(v))           => termToLit.get(t).exists(_ != v)
      case FEq(TLit(v), t)           => termToLit.get(t).exists(_ != v)
      case FNot(FEq(l, r)) if l == r => true
      case _                         => false
    }
    if (hasContradiction) None
    else
      Some(flat.filterNot {
        case FEq(l, r) if l == r   => true
        case FNot(FEq(t, TLit(v))) => termToLit.get(t).exists(_ != v)
        case FNot(FEq(TLit(v), t)) => termToLit.get(t).exists(_ != v)
        // normal completion from modeled internal method is default — strip
        case FEq(TTypeOf(TApp(fname, _)), TType(ty))
            if ty <= NormalT && Reify.isInternalMethod(fname) =>
          true
        case _ => false
      })
