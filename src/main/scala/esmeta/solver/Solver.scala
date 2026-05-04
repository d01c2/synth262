package esmeta.solver

import esmeta.ir.*
import esmeta.ty.*
import Formula.*, Term.*

type Goal = List[Formula]
type Witness = Map[String, String]

object Solver:
  def solve(goal: Goal, entryParams: List[String]): Option[Witness] =
    simplify(rewriteApps(goal)).flatMap(Reify(_, entryParams).witness)

  def rewriteApps(fs: Goal): Goal =
    val rewritten = fs
      .map(flatten)
      .map(stripCompletionWrappers)
      .flatMap(rewriteFormula)
      .map(unfoldTerms)
    if (rewritten != fs) rewriteApps(rewritten) else rewritten

  // --- Formula rewriting (manual AO models) ---

  private def rewriteFormula(f: Formula): List[Formula] = f match
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
    // typeof OrdinaryCreateFromConstructor: always succeeds
    case FEq(TTypeOf(TApp("OrdinaryCreateFromConstructor", _)), TType(ty))
        if ty <= NormalT =>
      List()
    // ToIntegerOrInfinity delegates to ToNumber
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
    // ValidateTypedArray delegates to RequireInternalSlot
    case FEq(TTypeOf(TApp("ValidateTypedArray", List(x, _))), TType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(
        FEq(
          TTypeOf(
            TApp("RequireInternalSlot", List(x, TLit(EStr("TypedArrayName")))),
          ),
          TType(ty),
        ),
      )
    // !(typeof RequireInternalSlot(x, slot) = Abrupt) → Normal case
    case FNot(
          FEq(
            TTypeOf(TApp("RequireInternalSlot", List(x, TLit(EStr(slot))))),
            TType(ty),
          ),
        ) if ty <= AbruptT =>
      List(FEq(TTypeOf(x), TType(ObjectT)), FExists(x, slot))
    // ToNumber value-comparison: unwrap and add Number type constraint
    case FEq(TApp("ToNumber", List(x)), v @ (_: TVar | _: TLit)) =>
      List(FEq(x, v), FEq(TTypeOf(x), TType(NumberT)))
    case FEq(v @ (_: TVar | _: TLit), TApp("ToNumber", List(x))) =>
      List(FEq(x, v), FEq(TTypeOf(x), TType(NumberT)))
    case FLt(TApp("ToNumber", List(x)), v @ (_: TVar | _: TLit)) =>
      List(FLt(x, v), FEq(TTypeOf(x), TType(NumberT)))
    case FLt(v @ (_: TVar | _: TLit), TApp("ToNumber", List(x))) =>
      List(FLt(v, x), FEq(TTypeOf(x), TType(NumberT)))
    case FNot(FEq(TApp("ToNumber", List(x)), v @ (_: TVar | _: TLit))) =>
      List(FNot(FEq(x, v)), FEq(TTypeOf(x), TType(NumberT)))
    case FNot(FEq(v @ (_: TVar | _: TLit), TApp("ToNumber", List(x)))) =>
      List(FNot(FEq(x, v)), FEq(TTypeOf(x), TType(NumberT)))
    case FNot(FLt(TApp("ToNumber", List(x)), v @ (_: TVar | _: TLit))) =>
      List(FNot(FLt(x, v)), FEq(TTypeOf(x), TType(NumberT)))
    case FNot(FLt(v @ (_: TVar | _: TLit), TApp("ToNumber", List(x)))) =>
      List(FNot(FLt(v, x)), FEq(TTypeOf(x), TType(NumberT)))
    // General FNot: recurse into inner
    case FNot(inner) =>
      rewriteFormula(inner) match
        case List(r) if r != inner => List(FNot(r))
        case _                     => List(f)
    case _ => List(f)

  // --- Term-level normalization ---

  private def stripCompletionWrappers(f: Formula): Formula = f match
    case FNot(inner)   => FNot(stripCompletionWrappers(inner))
    case FEq(l, r)     => FEq(stripCompletion(l), stripCompletion(r))
    case FLt(l, r)     => FLt(stripCompletion(l), stripCompletion(r))
    case FExists(b, k) => FExists(stripCompletion(b), k)
  private def stripCompletion(t: Term): Term = t match
    case TApp("Completion", List(x)) => stripCompletion(x)
    case TField(inner, "Value")      => stripCompletion(inner)
    case TField(base, k)             => TField(stripCompletion(base), k)
    case TApp(op, args)              => TApp(op, args.map(stripCompletion))
    case TTypeOf(inner)              => TTypeOf(stripCompletion(inner))
    case _                           => t

  private def unfoldTerms(f: Formula): Formula = f match
    case FEq(TField(base, "Type"), TLit(EEnum(e))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(TTypeOf(unfoldTermSafe(base)), TType(ty))
    case FEq(TLit(EEnum(e)), TField(base, "Type")) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(TTypeOf(unfoldTermSafe(base)), TType(ty))
    case FNot(inner)   => FNot(unfoldTerms(inner))
    case FEq(l, r)     => FEq(unfoldTerm(l), unfoldTerm(r))
    case FLt(l, r)     => FLt(unfoldTerm(l), unfoldTerm(r))
    case FExists(b, k) => FExists(unfoldTerm(b), k)

  private def unfoldTerm(t: Term): Term = t match
    case TApp("Completion", List(x)) => unfoldTerm(x)
    case TField(inner, "Value")      => unfoldTerm(inner)
    case TApp("LengthOfArrayLike", List(x)) =>
      TField(unfoldTerm(x), "length")
    case TApp("GetMethod", List(v, TLit(EStr(p)))) =>
      TField(unfoldTerm(v), p)
    case TApp("GetMethod", List(v, TField(_, p))) =>
      TField(unfoldTerm(v), p)
    case TApp("ToNumber", List(x))               => unfoldTerm(x)
    case TApp("ToString", List(x))               => unfoldTerm(x)
    case TApp("ToObject", List(x))               => unfoldTerm(x)
    case TApp("RequireObjectCoercible", List(x)) => unfoldTerm(x)
    case TApp("ToPropertyKey", List(x))          => unfoldTerm(x)
    case TApp("ToIntegerOrInfinity", List(x)) =>
      TApp("ToNumber", List(unfoldTerm(x)))
    case TApp("ToLength", List(x)) =>
      TApp("ToIntegerOrInfinity", List(unfoldTerm(x)))
    case TApp("ToIndex", List(x)) =>
      TApp("ToIntegerOrInfinity", List(unfoldTerm(x)))
    case TTypeOf(inner)  => TTypeOf(unfoldTermSafe(inner))
    case TField(base, k) => TField(unfoldTerm(base), k)
    case TApp(op, args)  => TApp(op, args.map(unfoldTerm))
    case TList(elems)    => TList(elems.map(unfoldTerm))
    case _               => t

  private def unfoldTermSafe(t: Term): Term = t match
    case TApp("Completion", List(x)) => unfoldTermSafe(x)
    case TField(inner, "Value")      => unfoldTermSafe(inner)
    case TApp("LengthOfArrayLike", List(x)) =>
      TField(unfoldTermSafe(x), "length")
    case TField(base, k) => TField(unfoldTermSafe(base), k)
    case TApp(op, args)  => TApp(op, args.map(unfoldTermSafe))
    case TTypeOf(inner)  => TTypeOf(unfoldTermSafe(inner))
    case _               => t

  // --- Simplification ---

  private def flatten(f: Formula): Formula = f match
    case FNot(FNot(inner)) => flatten(inner)
    case FNot(FEq(TTypeOf(t), TType(ty))) if ty <= NormalT =>
      FEq(TTypeOf(t), TType(AbruptT))
    case FNot(FEq(TTypeOf(t), TType(ty))) if ty <= AbruptT =>
      FEq(TTypeOf(t), TType(NormalT))
    case FNot(inner) => FNot(flatten(inner))
    case FEq(TApp(UOp.Not, List(t)), TLit(EBool(b))) =>
      flatten(FEq(t, TLit(EBool(!b))))
    case FEq(TLit(EBool(b)), TApp(UOp.Not, List(t))) =>
      flatten(FEq(t, TLit(EBool(!b))))
    case FEq(TApp(BOp.Eq, List(l, r)), TLit(EBool(b))) =>
      if (b) FEq(l, r) else FNot(FEq(l, r))
    case FEq(TLit(EBool(b)), TApp(BOp.Eq, List(l, r))) =>
      if (b) FEq(l, r) else FNot(FEq(l, r))
    case FEq(TApp(BOp.Lt, List(l, r)), TLit(EBool(b))) =>
      if (b) FLt(l, r) else FNot(FLt(l, r))
    case FEq(TLit(EBool(b)), TApp(BOp.Lt, List(l, r))) =>
      if (b) FLt(l, r) else FNot(FLt(l, r))
    case _ => f

  private def simplify(fs: List[Formula]): Option[List[Formula]] =
    val flat = fs.map(flatten)
    val termToLit: Map[Term, LiteralExpr] = flat.collect {
      case FEq(t, TLit(v)) => t -> v
      case FEq(TLit(v), t) => t -> v
    }.toMap
    val termToType: Map[Term, ValueTy] = flat.collect {
      case FEq(TTypeOf(t), TType(ty)) => t -> ty
    }.toMap
    val hasContradiction = flat.exists {
      case FEq(TLit(a), TLit(b))     => a != b
      case FEq(t, TLit(v))           => termToLit.get(t).exists(_ != v)
      case FEq(TLit(v), t)           => termToLit.get(t).exists(_ != v)
      case FNot(FEq(l, r)) if l == r => true
      case _                         => false
    } || termToLit.exists { (t, lit) =>
      termToType.get(t).exists { ty =>
        !(ty <= NormalT) && !(ty <= AbruptT) && (litType(lit) && ty).isBottom
      }
    }
    if (hasContradiction) None
    else {
      Some(flat.filterNot {
        case FEq(l, r) if l == r   => true
        case FNot(FEq(t, TLit(v))) => termToLit.get(t).exists(_ != v)
        case FNot(FEq(TLit(v), t)) => termToLit.get(t).exists(_ != v)
        case FEq(TTypeOf(TApp(fname: String, _)), TType(ty))
            if ty <= NormalT && Reify.isInternalMethod(fname) =>
          true
        case _ => false
      })
    }

  private def litType(lit: LiteralExpr): ValueTy = lit match
    case _: EMath | _: ENumber | _: EInfinity => NumberT
    case _: EStr                              => StrT
    case _: EBool                             => BoolT
    case _: ENull                             => NullT
    case _: EUndef                            => UndefT
    case _: EBigInt                           => BigIntT
    case _                                    => AnyT
