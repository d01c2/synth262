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
    val eliminated = eliminate(rewriteApps(goal), entrySet)
    simplify(eliminated).flatMap(Reify(_, entryParams).witness)

  // Rewrite known AO calls into equivalent type constraints
  // FIXME: Manual modeling
  def rewriteApps(fs: Goal): Goal =
    val rewritten = fs.map(flatten).flatMap(rewriteFormula).map(unfoldTerms)
    if (rewritten != fs) rewriteApps(rewritten) else rewritten

  // term-level normalization applied to formulas
  private def unfoldTerms(f: Formula): Formula = f match
    case FNot(inner)   => FNot(unfoldTerms(inner))
    case FEq(l, r)     => FEq(unfoldTerm(l), unfoldTerm(r))
    case FLt(l, r)     => FLt(unfoldTerm(l), unfoldTerm(r))
    case FExists(b, k) => FExists(unfoldTerm(b), k)

  private def unfoldTerm(t: Term): Term = t match
    // IR artifacts (always safe)
    case TApp("Completion", List(x)) => unfoldTerm(x)
    case TField(inner, "Value")      => unfoldTerm(inner)
    // structural unfold (always safe)
    case TApp("LengthOfArrayLike", List(x)) =>
      TField(unfoldTerm(x), "length")
    case TApp("GetMethod", List(v, TLit(EStr(p)))) =>
      TField(unfoldTerm(v), p)
    case TApp("GetMethod", List(v, TField(_, p))) =>
      TField(unfoldTerm(v), p)
    // leaf unfold: AO(x) → x (safe outside TTypeOf)
    case TApp("ToNumber", List(x))               => unfoldTerm(x)
    case TApp("ToString", List(x))               => unfoldTerm(x)
    case TApp("ToObject", List(x))               => unfoldTerm(x)
    case TApp("RequireObjectCoercible", List(x)) => unfoldTerm(x)
    case TApp("ToPropertyKey", List(x))          => unfoldTerm(x)
    // one-level delegating unfold
    case TApp("ToIntegerOrInfinity", List(x)) =>
      TApp("ToNumber", List(unfoldTerm(x)))
    case TApp("ToLength", List(x)) =>
      TApp("ToIntegerOrInfinity", List(unfoldTerm(x)))
    case TApp("ToIndex", List(x)) =>
      TApp("ToIntegerOrInfinity", List(unfoldTerm(x)))
    // TTypeOf: do NOT unfold type-conversion AOs inside
    case TTypeOf(inner) => TTypeOf(unfoldTermSafe(inner))
    // recurse
    case TField(base, k) => TField(unfoldTerm(base), k)
    case TApp(op, args)  => TApp(op, args.map(unfoldTerm))
    case TList(elems)    => TList(elems.map(unfoldTerm))
    case TUOp(op, x)     => TUOp(op, unfoldTerm(x))
    case TBOp(op, l, r)  => TBOp(op, unfoldTerm(l), unfoldTerm(r))
    case TVOp(op, args)  => TVOp(op, args.map(unfoldTerm))
    case TSizeOf(x)      => TSizeOf(unfoldTerm(x))
    case _               => t

  // safe unfold: only IR artifacts and structural, no type-conversion
  private def unfoldTermSafe(t: Term): Term = t match
    case TApp("Completion", List(x)) => unfoldTermSafe(x)
    case TField(inner, "Value")      => unfoldTermSafe(inner)
    case TApp("LengthOfArrayLike", List(x)) =>
      TField(unfoldTermSafe(x), "length")
    case TField(base, k) => TField(unfoldTermSafe(base), k)
    case TApp(op, args)  => TApp(op, args.map(unfoldTermSafe))
    case TTypeOf(inner)  => TTypeOf(unfoldTermSafe(inner))
    case _               => t

  private def rewriteFormula(f: Formula): List[Formula] = f match
    // === Leaf type rules (direct to input constraints) ===
    // IsCallable(x) == true/false
    case FEq(TApp("IsCallable", List(x)), TLit(EBool(b))) =>
      val eq = FEq(TTypeOf(x), TType(FunctionT))
      List(if (b) eq else FNot(eq))
    // IsConstructor(x) == true/false
    case FEq(TApp("IsConstructor", List(x)), TLit(EBool(b))) =>
      val eq = FEq(TTypeOf(x), TType(ConstructorT))
      List(if (b) eq else FNot(eq))
    // IsRegExp(x) == true/false
    case FEq(TApp("IsRegExp", List(x)), TLit(EBool(true))) =>
      List(FEq(TTypeOf(x), TType(ObjectT)), FExists(x, "RegExpMatcher"))
    case FEq(TApp("IsRegExp", List(x)), TLit(EBool(false))) =>
      List()
    // typeof IsRegExp: Normal (Get(@@match) rarely throws)
    case FEq(TTypeOf(TApp("IsRegExp", _)), TType(ty)) if ty <= NormalT =>
      List()
    // typeof ToObject(x): throws on Undef|Null
    case FEq(TTypeOf(TApp("ToObject", List(x))), TType(ty)) if ty <= AbruptT =>
      List(FEq(TTypeOf(x), TType(UndefT || NullT)))
    case FEq(TTypeOf(TApp("ToObject", List(x))), TType(ty)) if ty <= NormalT =>
      List(FNot(FEq(TTypeOf(x), TType(UndefT || NullT))))
    // typeof ToNumber(x): throws on Symbol|BigInt
    case FEq(TTypeOf(TApp("ToNumber", List(x))), TType(ty)) if ty <= AbruptT =>
      List(FEq(TTypeOf(x), TType(SymbolT || BigIntT)))
    case FEq(TTypeOf(TApp("ToNumber", List(x))), TType(ty)) if ty <= NormalT =>
      List(FNot(FEq(TTypeOf(x), TType(SymbolT || BigIntT))))
    // typeof ToString(x): throws on Symbol
    case FEq(TTypeOf(TApp("ToString", List(x))), TType(ty)) if ty <= AbruptT =>
      List(FEq(TTypeOf(x), TType(SymbolT)))
    case FEq(TTypeOf(TApp("ToString", List(x))), TType(ty)) if ty <= NormalT =>
      List(FNot(FEq(TTypeOf(x), TType(SymbolT))))
    // typeof RequireObjectCoercible(x): throws on Undef|Null
    case FEq(TTypeOf(TApp("RequireObjectCoercible", List(x))), TType(ty))
        if ty <= AbruptT =>
      List(FEq(TTypeOf(x), TType(UndefT || NullT)))
    case FEq(TTypeOf(TApp("RequireObjectCoercible", List(x))), TType(ty))
        if ty <= NormalT =>
      List(FNot(FEq(TTypeOf(x), TType(UndefT || NullT))))
    case FEq(TTypeOf(TApp("RequireObjectCoercible", List(x))), TType(ty)) =>
      List(FEq(TTypeOf(x), TType(ty)))
    // typeof RequireInternalSlot(x, slot): throws if not Object or missing slot
    case FEq(
          TTypeOf(TApp("RequireInternalSlot", List(x, TLit(EStr(slot))))),
          TType(ty),
        ) if ty <= NormalT =>
      List(FEq(TTypeOf(x), TType(ObjectT)), FExists(x, slot))
    case FEq(
          TTypeOf(TApp("RequireInternalSlot", List(x, TLit(EStr(slot))))),
          TType(ty),
        ) if ty <= AbruptT =>
      List(FNot(FEq(TTypeOf(x), TType(ObjectT))))
    // typeof OrdinaryCreateFromConstructor: Normal (always succeeds)
    case FEq(TTypeOf(TApp("OrdinaryCreateFromConstructor", _)), TType(ty))
        if ty <= NormalT =>
      List()

    // === One-level type unfolds (delegate to another AO) ===
    // ToIntegerOrInfinity(x) delegates to ToNumber(x)
    case FEq(TTypeOf(TApp("ToIntegerOrInfinity", List(x))), TType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(FEq(TTypeOf(TApp("ToNumber", List(x))), TType(ty)))
    // ToLength delegates to ToIntegerOrInfinity
    case FEq(TTypeOf(TApp("ToLength", List(x))), TType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(FEq(TTypeOf(TApp("ToIntegerOrInfinity", List(x))), TType(ty)))
    // ToIndex delegates to ToIntegerOrInfinity
    case FEq(TTypeOf(TApp("ToIndex", List(x))), TType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(FEq(TTypeOf(TApp("ToIntegerOrInfinity", List(x))), TType(ty)))
    // ValidateTypedArray(x, _) delegates to RequireInternalSlot
    case FEq(TTypeOf(TApp("ValidateTypedArray", List(x, _))), TType(ty))
        if ty <= NormalT =>
      List(
        FEq(
          TTypeOf(
            TApp("RequireInternalSlot", List(x, TLit(EStr("TypedArrayName")))),
          ),
          TType(ty),
        ),
      )
    case FEq(TTypeOf(TApp("ValidateTypedArray", List(x, _))), TType(ty))
        if ty <= AbruptT =>
      List(
        FEq(
          TTypeOf(
            TApp("RequireInternalSlot", List(x, TLit(EStr("TypedArrayName")))),
          ),
          TType(ty),
        ),
      )

    // === sizeof constraints ===
    // sizeof(x) > 0: non-empty string → x != ""
    case FLt(TLit(EMath(n)), TSizeOf(x)) if n == 0 =>
      List(FNot(FEq(x, TLit(EStr("")))))
    // !(sizeof(x) > 0): empty string → x == ""
    case FNot(FLt(TLit(EMath(n)), TSizeOf(x))) if n == 0 =>
      List(FEq(x, TLit(EStr(""))))

    // === Explicit FNot patterns for multi-conjunct Normal cases ===
    // !(typeof RequireInternalSlot(x, slot) = Abrupt) → Normal case
    case FNot(
          FEq(
            TTypeOf(TApp("RequireInternalSlot", List(x, TLit(EStr(slot))))),
            TType(ty),
          ),
        ) if ty <= AbruptT =>
      List(FEq(TTypeOf(x), TType(ObjectT)), FExists(x, slot))

    // === General FNot unwrapping ===
    case FNot(inner) =>
      rewriteFormula(inner) match
        case List(r) if r != inner => List(FNot(r))
        case _                     => List(f)
    case f => List(f)

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

  // Flatten double negations, normalize completion types, promote boolean terms
  private def flatten(f: Formula): Formula = f match
    case FNot(FNot(inner)) => flatten(inner)
    case FNot(FEq(TTypeOf(t), TType(ty))) if ty <= NormalT =>
      FEq(TTypeOf(t), TType(AbruptT))
    case FNot(FEq(TTypeOf(t), TType(ty))) if ty <= AbruptT =>
      FEq(TTypeOf(t), TType(NormalT))
    case FNot(inner) => FNot(flatten(inner))
    // boolean term → formula promotion
    case FEq(TUOp(UOp.Not, t), TLit(EBool(b))) =>
      flatten(FEq(t, TLit(EBool(!b))))
    case FEq(TLit(EBool(b)), TUOp(UOp.Not, t)) =>
      flatten(FEq(t, TLit(EBool(!b))))
    case FEq(TBOp(BOp.Eq, l, r), TLit(EBool(b))) =>
      if (b) FEq(l, r) else FNot(FEq(l, r))
    case FEq(TLit(EBool(b)), TBOp(BOp.Eq, l, r)) =>
      if (b) FEq(l, r) else FNot(FEq(l, r))
    case FEq(TBOp(BOp.Lt, l, r), TLit(EBool(b))) =>
      if (b) FLt(l, r) else FNot(FLt(l, r))
    case FEq(TLit(EBool(b)), TBOp(BOp.Lt, l, r)) =>
      if (b) FLt(l, r) else FNot(FLt(l, r))
    case _ => f

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
