package esmeta.solver

import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*

type Goal = List[Formula]
type Witness = Map[Sym, String]

object Solver:
  def solve(goal: Goal, entryParams: List[Sym]): Option[Witness] =
    simplify(rewrite(goal)).flatMap(Reify(_, entryParams).witness)

  def rewrite(fs: Goal): Goal =
    val result = fs.map(normalize).flatMap(rewriteAO).map(reduceFormula)
    if (result != fs) rewrite(result) else result

  // structural normalization
  private def normalize(f: Formula): Formula =
    flatten(f) match
      case FNot(inner)   => FNot(normalize(inner))
      case FEq(l, r)     => FEq(stripCompletion(l), stripCompletion(r))
      case FLt(l, r)     => FLt(stripCompletion(l), stripCompletion(r))
      case FExists(b, k) => FExists(stripCompletion(b), k)

  private def flatten(f: Formula): Formula = f match
    case FNot(FNot(inner)) => flatten(inner)
    case FNot(FEq(SETypeOf(t), SEType(ty))) if ty <= NormalT =>
      FEq(SETypeOf(t), SEType(AbruptT))
    case FNot(FEq(SETypeOf(t), SEType(ty))) if ty <= AbruptT =>
      FEq(SETypeOf(t), SEType(NormalT))
    case FNot(inner) => FNot(flatten(inner))
    case FEq(SEApp(UOp.Not, List(t)), SELit(EBool(b))) =>
      flatten(FEq(t, SELit(EBool(!b))))
    case FEq(SELit(EBool(b)), SEApp(UOp.Not, List(t))) =>
      flatten(FEq(t, SELit(EBool(!b))))
    case FEq(SEApp(BOp.Eq, List(l, r)), SELit(EBool(b))) =>
      if (b) FEq(l, r) else FNot(FEq(l, r))
    case FEq(SELit(EBool(b)), SEApp(BOp.Eq, List(l, r))) =>
      if (b) FEq(l, r) else FNot(FEq(l, r))
    case FEq(SEApp(BOp.Lt, List(l, r)), SELit(EBool(b))) =>
      if (b) FLt(l, r) else FNot(FLt(l, r))
    case FEq(SELit(EBool(b)), SEApp(BOp.Lt, List(l, r))) =>
      if (b) FLt(l, r) else FNot(FLt(l, r))
    case _ => f

  private def stripCompletion(t: SymExpr): SymExpr = t match
    case SEApp("Completion", List(x))        => stripCompletion(x)
    case SEProj(inner, SELit(EStr("Value"))) => stripCompletion(inner)
    case SEProj(base, k)                     => SEProj(stripCompletion(base), k)
    case SEApp(op, args) => SEApp(op, args.map(stripCompletion))
    case SETypeOf(inner) => SETypeOf(stripCompletion(inner))
    case _               => t

  // manual AO application rewriting
  private def rewriteAO(f: Formula): List[Formula] = f match
    case FEq(SEApp("IsCallable", List(x)), SELit(EBool(b))) =>
      val eq = FEq(SETypeOf(x), SEType(FunctionT))
      List(if (b) eq else FNot(eq))
    case FEq(SEApp("IsConstructor", List(x)), SELit(EBool(b))) =>
      val eq = FEq(SETypeOf(x), SEType(ConstructorT))
      List(if (b) eq else FNot(eq))
    case FEq(SEApp("IsRegExp", List(x)), SELit(EBool(true))) =>
      List(
        FEq(SETypeOf(x), SEType(ObjectT)),
        FExists(x, SELit(EStr("RegExpMatcher"))),
      )
    case FEq(SEApp("IsRegExp", List(x)), SELit(EBool(false))) =>
      List()
    case FEq(SETypeOf(SEApp("IsRegExp", _)), SEType(ty)) if ty <= NormalT =>
      List()
    case FEq(SETypeOf(SEApp("ToObject", List(x))), SEType(ty))
        if ty <= AbruptT =>
      List(FEq(SETypeOf(x), SEType(UndefT || NullT)))
    case FEq(SETypeOf(SEApp("ToObject", List(x))), SEType(ty))
        if ty <= NormalT =>
      List(FNot(FEq(SETypeOf(x), SEType(UndefT || NullT))))
    case FEq(SETypeOf(SEApp("ToNumber", List(x))), SEType(ty))
        if ty <= AbruptT =>
      List(FEq(SETypeOf(x), SEType(SymbolT || BigIntT)))
    case FEq(SETypeOf(SEApp("ToNumber", List(x))), SEType(ty))
        if ty <= NormalT =>
      List(FNot(FEq(SETypeOf(x), SEType(SymbolT || BigIntT))))
    case FEq(SETypeOf(SEApp("ToString", List(x))), SEType(ty))
        if ty <= AbruptT =>
      List(FEq(SETypeOf(x), SEType(SymbolT)))
    case FEq(SETypeOf(SEApp("ToString", List(x))), SEType(ty))
        if ty <= NormalT =>
      List(FNot(FEq(SETypeOf(x), SEType(SymbolT))))
    case FEq(SETypeOf(SEApp("RequireObjectCoercible", List(x))), SEType(ty))
        if ty <= AbruptT =>
      List(FEq(SETypeOf(x), SEType(UndefT || NullT)))
    case FEq(SETypeOf(SEApp("RequireObjectCoercible", List(x))), SEType(ty))
        if ty <= NormalT =>
      List(FNot(FEq(SETypeOf(x), SEType(UndefT || NullT))))
    case FEq(SETypeOf(SEApp("RequireObjectCoercible", List(x))), SEType(ty)) =>
      List(FEq(SETypeOf(x), SEType(ty)))
    case FEq(
          SETypeOf(SEApp("RequireInternalSlot", List(x, SELit(EStr(slot))))),
          SEType(ty),
        ) if ty <= NormalT =>
      List(FEq(SETypeOf(x), SEType(ObjectT)), FExists(x, SELit(EStr(slot))))
    case FEq(
          SETypeOf(SEApp("RequireInternalSlot", List(x, SELit(EStr(slot))))),
          SEType(ty),
        ) if ty <= AbruptT =>
      List(FNot(FEq(SETypeOf(x), SEType(ObjectT))))
    case FEq(SETypeOf(SEApp("OrdinaryCreateFromConstructor", _)), SEType(ty))
        if ty <= NormalT =>
      List()
    case FEq(SETypeOf(SEApp("ToIntegerOrInfinity", List(x))), SEType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(FEq(SETypeOf(SEApp("ToNumber", List(x))), SEType(ty)))
    case FEq(SETypeOf(SEApp("ToLength", List(x))), SEType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(FEq(SETypeOf(SEApp("ToIntegerOrInfinity", List(x))), SEType(ty)))
    case FEq(SETypeOf(SEApp("ToIndex", List(x))), SEType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(FEq(SETypeOf(SEApp("ToIntegerOrInfinity", List(x))), SEType(ty)))
    case FEq(SETypeOf(SEApp("ValidateTypedArray", List(x, _))), SEType(ty))
        if ty <= AbruptT || ty <= NormalT =>
      List(
        FEq(
          SETypeOf(
            SEApp("RequireInternalSlot", List(x, SELit(EStr("TypedArrayName")))),
          ),
          SEType(ty),
        ),
      )
    case FNot(
          FEq(
            SETypeOf(SEApp("RequireInternalSlot", List(x, SELit(EStr(slot))))),
            SEType(ty),
          ),
        ) if ty <= AbruptT =>
      List(FEq(SETypeOf(x), SEType(ObjectT)), FExists(x, SELit(EStr(slot))))
    case FEq(SEApp("ToNumber", List(x)), v @ (_: SESym | _: SELit)) =>
      List(FEq(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FEq(v @ (_: SESym | _: SELit), SEApp("ToNumber", List(x))) =>
      List(FEq(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FLt(SEApp("ToNumber", List(x)), v @ (_: SESym | _: SELit)) =>
      List(FLt(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FLt(v @ (_: SESym | _: SELit), SEApp("ToNumber", List(x))) =>
      List(FLt(v, x), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FEq(SEApp("ToNumber", List(x)), v @ (_: SESym | _: SELit))) =>
      List(FNot(FEq(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FEq(v @ (_: SESym | _: SELit), SEApp("ToNumber", List(x)))) =>
      List(FNot(FEq(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FLt(SEApp("ToNumber", List(x)), v @ (_: SESym | _: SELit))) =>
      List(FNot(FLt(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FLt(v @ (_: SESym | _: SELit), SEApp("ToNumber", List(x)))) =>
      List(FNot(FLt(v, x)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(inner) =>
      rewriteAO(inner) match
        case List(r) if r != inner => List(FNot(r))
        case _                     => List(f)
    case _ => List(f)

  // expression reduction

  private def reduceFormula(f: Formula): Formula = f match
    case FEq(SEProj(base, SELit(EStr("Type"))), SELit(EEnum(e))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(reduce(base, safe = true)), SEType(ty))
    case FEq(SELit(EEnum(e)), SEProj(base, SELit(EStr("Type")))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(reduce(base, safe = true)), SEType(ty))
    case FNot(inner)   => FNot(reduceFormula(inner))
    case FEq(l, r)     => FEq(reduce(l), reduce(r))
    case FLt(l, r)     => FLt(reduce(l), reduce(r))
    case FExists(b, k) => FExists(reduce(b), k)

  private def reduce(t: SymExpr, safe: Boolean = false): SymExpr = t match
    case SEApp("LengthOfArrayLike", List(x)) =>
      SEProj(reduce(x, safe), SELit(EStr("length")))
    case SEApp("GetMethod", List(v, SELit(EStr(p)))) if !safe =>
      SEProj(reduce(v), SELit(EStr(p)))
    case SEApp("GetMethod", List(v, SEProj(_, p))) if !safe =>
      SEProj(reduce(v), p)
    case SEApp("ToNumber", List(x)) if !safe               => reduce(x)
    case SEApp("ToString", List(x)) if !safe               => reduce(x)
    case SEApp("ToObject", List(x)) if !safe               => reduce(x)
    case SEApp("RequireObjectCoercible", List(x)) if !safe => reduce(x)
    case SEApp("ToPropertyKey", List(x)) if !safe          => reduce(x)
    case SEApp("ToIntegerOrInfinity", List(x)) if !safe =>
      SEApp("ToNumber", List(reduce(x)))
    case SEApp("ToLength", List(x)) if !safe =>
      SEApp("ToIntegerOrInfinity", List(reduce(x)))
    case SEApp("ToIndex", List(x)) if !safe =>
      SEApp("ToIntegerOrInfinity", List(reduce(x)))
    case SETypeOf(inner) => SETypeOf(reduce(inner, safe = true))
    case SEProj(base, k) => SEProj(reduce(base, safe), k)
    case SEApp(op, args) => SEApp(op, args.map(reduce(_, safe)))
    case SEList(elems)   => SEList(elems.map(reduce(_, safe)))
    case _               => t

  // simplification

  def simplify(fs: List[Formula]): Option[List[Formula]] =
    val norm = fs.map(normalize)
    val termToLit: Map[SymExpr, LiteralExpr] = norm.collect {
      case FEq(t, SELit(v)) => t -> v
      case FEq(SELit(v), t) => t -> v
    }.toMap
    val termToType: Map[SymExpr, ValueTy] = norm.collect {
      case FEq(SETypeOf(t), SEType(ty)) => t -> ty
    }.toMap
    val hasContradiction = norm.exists {
      case FEq(SELit(a), SELit(b))   => a != b
      case FEq(t, SELit(v))          => termToLit.get(t).exists(_ != v)
      case FEq(SELit(v), t)          => termToLit.get(t).exists(_ != v)
      case FNot(FEq(l, r)) if l == r => true
      case FNot(FEq(t, SELit(v)))    => termToLit.get(t).exists(_ == v)
      case FNot(FEq(SELit(v), t))    => termToLit.get(t).exists(_ == v)
      case FLt(l, r) if l == r       => true
      case _                         => false
    } || termToLit.exists { (t, lit) =>
      termToType.get(t).exists { ty =>
        !(ty <= NormalT) && !(ty <= AbruptT) && (litType(lit) && ty).isBottom
      }
    } || norm
      .collect {
        case FEq(SETypeOf(t), SEType(ty))
            if !(ty <= NormalT) && !(ty <= AbruptT) =>
          (t, ty)
      }
      .groupMap(_._1)(_._2)
      .exists { (_, tys) =>
        tys.size > 1 && tys.reduce(_ && _).isBottom
      }
    if (hasContradiction) None
    else
      Some(norm.filterNot {
        case FEq(l, r) if l == r    => true
        case FNot(FEq(t, SELit(v))) => termToLit.get(t).exists(_ != v)
        case FNot(FEq(SELit(v), t)) => termToLit.get(t).exists(_ != v)
        case FEq(SETypeOf(SEApp(fname: String, _)), SEType(ty))
            if ty <= NormalT && Reify.isInternalMethod(fname) =>
          true
        case _ => false
      })

  private def litType(lit: LiteralExpr): ValueTy = lit match
    case _: EMath | _: ENumber | _: EInfinity => NumberT
    case _: EStr                              => StrT
    case _: EBool                             => BoolT
    case _: ENull                             => NullT
    case _: EUndef                            => UndefT
    case _: EBigInt                           => BigIntT
    case _: ECodeUnit                         => CodeUnitT
    case _                                    => AnyT
