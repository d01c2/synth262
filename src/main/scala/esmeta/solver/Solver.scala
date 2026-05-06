package esmeta.solver

import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*

type Goal = List[Formula]
type Witness = Map[SymId, String]

object Solver:
  def solve(goal: Goal, entryParams: List[SymId]): Option[Witness] =
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
    case FEq(App("IsCallable", List(x)), Lit(EBool(b))) =>
      val eq = FEq(TypeOf(x), SType(FunctionT))
      List(if (b) eq else FNot(eq))
    // IsConstructor(x) == true/false
    case FEq(App("IsConstructor", List(x)), Lit(EBool(b))) =>
      val eq = FEq(TypeOf(x), SType(ConstructorT))
      List(if (b) eq else FNot(eq))
    // IsRegExp(x) == true/false
    case FEq(App("IsRegExp", List(x)), Lit(EBool(true))) =>
      List(
        FEq(TypeOf(x), SType(ObjectT)),
        FExists(x, Lit(EStr("RegExpMatcher"))),
      )
    case FEq(App("IsRegExp", List(x)), Lit(EBool(false))) =>
      List()
    // typeof IsRegExp: Normal (Get(@@match) rarely throws)
    case FEq(TypeOf(App("IsRegExp", _)), SType(ty)) if ty <= NormalT =>
      List()
    // typeof ToObject(x): throws on Undef|Null
    case FEq(TypeOf(App("ToObject", List(x))), SType(ty)) if ty <= AbruptT =>
      List(FEq(TypeOf(x), SType(UndefT || NullT)))
    case FEq(TypeOf(App("ToObject", List(x))), SType(ty)) if ty <= NormalT =>
      List(FNot(FEq(TypeOf(x), SType(UndefT || NullT))))
    // typeof ToNumber(x): throws on Symbol|BigInt
    case FEq(TypeOf(App("ToNumber", List(x))), SType(ty)) if ty <= AbruptT =>
      List(FEq(TypeOf(x), SType(SymbolT || BigIntT)))
    case FEq(TypeOf(App("ToNumber", List(x))), SType(ty)) if ty <= NormalT =>
      List(FNot(FEq(TypeOf(x), SType(SymbolT || BigIntT))))
    // typeof ToString(x): throws on Symbol
    case FEq(TypeOf(App("ToString", List(x))), SType(ty)) if ty <= AbruptT =>
      List(FEq(TypeOf(x), SType(SymbolT)))
    case FEq(TypeOf(App("ToString", List(x))), SType(ty)) if ty <= NormalT =>
      List(FNot(FEq(TypeOf(x), SType(SymbolT))))
    // typeof RequireObjectCoercible(x): throws on Undef|Null
    case FEq(TypeOf(App("RequireObjectCoercible", List(x))), SType(ty))
        if ty <= AbruptT =>
      List(FEq(TypeOf(x), SType(UndefT || NullT)))
    case FEq(TypeOf(App("RequireObjectCoercible", List(x))), SType(ty))
        if ty <= NormalT =>
      List(FNot(FEq(TypeOf(x), SType(UndefT || NullT))))
    case FEq(TypeOf(App("RequireObjectCoercible", List(x))), SType(ty)) =>
      List(FEq(TypeOf(x), SType(ty)))
    // typeof RequireInternalSlot(x, slot): throws if not Object or missing slot
    case FEq(
          TypeOf(App("RequireInternalSlot", List(x, Lit(EStr(slot))))),
          SType(ty),
        ) if ty <= NormalT =>
      List(FEq(TypeOf(x), SType(ObjectT)), FExists(x, Lit(EStr(slot))))
    case FEq(
          TypeOf(App("RequireInternalSlot", List(x, Lit(EStr(slot))))),
          SType(ty),
        ) if ty <= AbruptT =>
      List(FNot(FEq(TypeOf(x), SType(ObjectT))))
    // typeof OrdinaryCreateFromConstructor: always succeeds
    case FEq(TypeOf(App("OrdinaryCreateFromConstructor", _)), SType(ty))
        if ty <= NormalT =>
      List()
    // ToIntegerOrInfinity delegates to ToNumber
    case FEq(TypeOf(App("ToIntegerOrInfinity", List(x))), SType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(FEq(TypeOf(App("ToNumber", List(x))), SType(ty)))
    // ToLength delegates to ToIntegerOrInfinity
    case FEq(TypeOf(App("ToLength", List(x))), SType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(FEq(TypeOf(App("ToIntegerOrInfinity", List(x))), SType(ty)))
    // ToIndex delegates to ToIntegerOrInfinity
    case FEq(TypeOf(App("ToIndex", List(x))), SType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(FEq(TypeOf(App("ToIntegerOrInfinity", List(x))), SType(ty)))
    // ValidateTypedArray delegates to RequireInternalSlot
    case FEq(TypeOf(App("ValidateTypedArray", List(x, _))), SType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(
        FEq(
          TypeOf(
            App("RequireInternalSlot", List(x, Lit(EStr("TypedArrayName")))),
          ),
          SType(ty),
        ),
      )
    // !(typeof RequireInternalSlot(x, slot) = Abrupt) → Normal case
    case FNot(
          FEq(
            TypeOf(App("RequireInternalSlot", List(x, Lit(EStr(slot))))),
            SType(ty),
          ),
        ) if ty <= AbruptT =>
      List(FEq(TypeOf(x), SType(ObjectT)), FExists(x, Lit(EStr(slot))))
    // ToNumber value-comparison: unwrap and add Number type constraint
    case FEq(App("ToNumber", List(x)), v @ (_: Sym | _: Lit)) =>
      List(FEq(x, v), FEq(TypeOf(x), SType(NumberT)))
    case FEq(v @ (_: Sym | _: Lit), App("ToNumber", List(x))) =>
      List(FEq(x, v), FEq(TypeOf(x), SType(NumberT)))
    case FLt(App("ToNumber", List(x)), v @ (_: Sym | _: Lit)) =>
      List(FLt(x, v), FEq(TypeOf(x), SType(NumberT)))
    case FLt(v @ (_: Sym | _: Lit), App("ToNumber", List(x))) =>
      List(FLt(v, x), FEq(TypeOf(x), SType(NumberT)))
    case FNot(FEq(App("ToNumber", List(x)), v @ (_: Sym | _: Lit))) =>
      List(FNot(FEq(x, v)), FEq(TypeOf(x), SType(NumberT)))
    case FNot(FEq(v @ (_: Sym | _: Lit), App("ToNumber", List(x)))) =>
      List(FNot(FEq(x, v)), FEq(TypeOf(x), SType(NumberT)))
    case FNot(FLt(App("ToNumber", List(x)), v @ (_: Sym | _: Lit))) =>
      List(FNot(FLt(x, v)), FEq(TypeOf(x), SType(NumberT)))
    case FNot(FLt(v @ (_: Sym | _: Lit), App("ToNumber", List(x)))) =>
      List(FNot(FLt(v, x)), FEq(TypeOf(x), SType(NumberT)))
    // General FNot: recurse into inner
    case FNot(inner) =>
      rewriteFormula(inner) match
        case List(r) if r != inner => List(FNot(r))
        case _                     => List(f)
    case _ => List(f)

  // --- expression-level normalization ---

  private def stripCompletionWrappers(f: Formula): Formula = f match
    case FNot(inner)   => FNot(stripCompletionWrappers(inner))
    case FEq(l, r)     => FEq(stripCompletion(l), stripCompletion(r))
    case FLt(l, r)     => FLt(stripCompletion(l), stripCompletion(r))
    case FExists(b, k) => FExists(stripCompletion(b), k)
  private def stripCompletion(t: SymExpr): SymExpr = t match
    case App("Completion", List(x))      => stripCompletion(x)
    case Proj(inner, Lit(EStr("Value"))) => stripCompletion(inner)
    case Proj(base, k)                   => Proj(stripCompletion(base), k)
    case App(op, args)                   => App(op, args.map(stripCompletion))
    case TypeOf(inner)                   => TypeOf(stripCompletion(inner))
    case _                               => t

  private def unfoldTerms(f: Formula): Formula = f match
    case FEq(Proj(base, Lit(EStr("Type"))), Lit(EEnum(e))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(TypeOf(unfoldSafe(base)), SType(ty))
    case FEq(Lit(EEnum(e)), Proj(base, Lit(EStr("Type")))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(TypeOf(unfoldSafe(base)), SType(ty))
    case FNot(inner)   => FNot(unfoldTerms(inner))
    case FEq(l, r)     => FEq(unfold(l), unfold(r))
    case FLt(l, r)     => FLt(unfold(l), unfold(r))
    case FExists(b, k) => FExists(unfold(b), k)

  private def unfold(t: SymExpr): SymExpr = t match
    case App("Completion", List(x))      => unfold(x)
    case Proj(inner, Lit(EStr("Value"))) => unfold(inner)
    case App("LengthOfArrayLike", List(x)) =>
      Proj(unfold(x), Lit(EStr("length")))
    case App("GetMethod", List(v, Lit(EStr(p)))) =>
      Proj(unfold(v), Lit(EStr(p)))
    case App("GetMethod", List(v, Proj(_, p))) =>
      Proj(unfold(v), p)
    case App("ToNumber", List(x))               => unfold(x)
    case App("ToString", List(x))               => unfold(x)
    case App("ToObject", List(x))               => unfold(x)
    case App("RequireObjectCoercible", List(x)) => unfold(x)
    case App("ToPropertyKey", List(x))          => unfold(x)
    case App("ToIntegerOrInfinity", List(x)) =>
      App("ToNumber", List(unfold(x)))
    case App("ToLength", List(x)) =>
      App("ToIntegerOrInfinity", List(unfold(x)))
    case App("ToIndex", List(x)) =>
      App("ToIntegerOrInfinity", List(unfold(x)))
    case TypeOf(inner) => TypeOf(unfoldSafe(inner))
    case Proj(base, k) => Proj(unfold(base), k)
    case App(op, args) => App(op, args.map(unfold))
    case SList(elems)  => SList(elems.map(unfold))
    case _             => t

  private def unfoldSafe(t: SymExpr): SymExpr = t match
    case App("Completion", List(x))      => unfoldSafe(x)
    case Proj(inner, Lit(EStr("Value"))) => unfoldSafe(inner)
    case App("LengthOfArrayLike", List(x)) =>
      Proj(unfoldSafe(x), Lit(EStr("length")))
    case Proj(base, k) => Proj(unfoldSafe(base), k)
    case App(op, args) => App(op, args.map(unfoldSafe))
    case TypeOf(inner) => TypeOf(unfoldSafe(inner))
    case _             => t

  // --- Simplification ---

  private def flatten(f: Formula): Formula = f match
    case FNot(FNot(inner)) => flatten(inner)
    case FNot(FEq(TypeOf(t), SType(ty))) if ty <= NormalT =>
      FEq(TypeOf(t), SType(AbruptT))
    case FNot(FEq(TypeOf(t), SType(ty))) if ty <= AbruptT =>
      FEq(TypeOf(t), SType(NormalT))
    case FNot(inner) => FNot(flatten(inner))
    case FEq(App(UOp.Not, List(t)), Lit(EBool(b))) =>
      flatten(FEq(t, Lit(EBool(!b))))
    case FEq(Lit(EBool(b)), App(UOp.Not, List(t))) =>
      flatten(FEq(t, Lit(EBool(!b))))
    case FEq(App(BOp.Eq, List(l, r)), Lit(EBool(b))) =>
      if (b) FEq(l, r) else FNot(FEq(l, r))
    case FEq(Lit(EBool(b)), App(BOp.Eq, List(l, r))) =>
      if (b) FEq(l, r) else FNot(FEq(l, r))
    case FEq(App(BOp.Lt, List(l, r)), Lit(EBool(b))) =>
      if (b) FLt(l, r) else FNot(FLt(l, r))
    case FEq(Lit(EBool(b)), App(BOp.Lt, List(l, r))) =>
      if (b) FLt(l, r) else FNot(FLt(l, r))
    case _ => f

  private def simplify(fs: List[Formula]): Option[List[Formula]] =
    val flat = fs.map(flatten)
    val termToLit: Map[SymExpr, LiteralExpr] = flat.collect {
      case FEq(t, Lit(v)) => t -> v
      case FEq(Lit(v), t) => t -> v
    }.toMap
    val termToType: Map[SymExpr, ValueTy] = flat.collect {
      case FEq(TypeOf(t), SType(ty)) => t -> ty
    }.toMap
    val hasContradiction = flat.exists {
      case FEq(Lit(a), Lit(b))       => a != b
      case FEq(t, Lit(v))            => termToLit.get(t).exists(_ != v)
      case FEq(Lit(v), t)            => termToLit.get(t).exists(_ != v)
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
        case FEq(l, r) if l == r  => true
        case FNot(FEq(t, Lit(v))) => termToLit.get(t).exists(_ != v)
        case FNot(FEq(Lit(v), t)) => termToLit.get(t).exists(_ != v)
        case FEq(TypeOf(App(fname: String, _)), SType(ty))
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
