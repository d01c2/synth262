package esmeta.solver

import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*

object RewriteRules:

  // ---------------------------------------------------------------------------
  // Declarative rule tables
  // ---------------------------------------------------------------------------

  // Predicate(x) == b  →  typeof(x) == ty  (negated when !b)
  val predicateType: Map[String, ValueTy] = Map(
    "IsCallable" -> FunctionT,
    "IsConstructor" -> ConstructorT,
    "IsArray" -> RecordT("Array"),
    "CanBeHeldWeakly" -> ObjectT,
    "IsConcatSpreadable" -> RecordT("Array"),
  )

  // typeof(AO(x)) <= Abrupt  →  typeof(x) == condTy
  // typeof(AO(x)) <= Normal  →  typeof(x) != condTy
  val abruptCond: Map[String, ValueTy] = Map(
    "ToObject" -> (UndefT || NullT),
    "ToNumber" -> (SymbolT || BigIntT),
    "ToString" -> SymbolT,
    "RequireObjectCoercible" -> (UndefT || NullT),
  )

  // typeof(AO(x)) <= Normal  →  typeof(x) == condTy  (inverse of abruptCond)
  // typeof(AO(x)) <= Abrupt  →  typeof(x) != condTy
  val normalCond: Map[String, ValueTy] = Map(
    "ThisNumberValue" -> NumberT,
    "ThisBooleanValue" -> BoolT,
    "ThisStringValue" -> StrT,
    "ThisBigIntValue" -> BigIntT,
    "ThisSymbolValue" -> SymbolT,
    "ToBigInt" -> (BigIntT || BoolT || StrT),
  )

  // typeof(AO(x)) <= ty  →  typeof(delegate(x)) <= ty
  val completionDeleg: Map[String, String] = Map(
    "ToIntegerOrInfinity" -> "ToNumber",
    "ToLength" -> "ToIntegerOrInfinity",
    "ToIndex" -> "ToIntegerOrInfinity",
  )

  // typeof(AO(...)) <= Normal  →  List()  (always succeeds)
  val alwaysNormal: Set[String] = Set(
    "OrdinaryCreateFromConstructor",
    "ArrayCreate",
    "InstallErrorCause",
    "IsArray",
    "ToBoolean",
    "ArraySpeciesCreate",
    "CreateDataPropertyOrThrow",
    "CreateDataProperty",
  )

  // AO(x) reduces to x (safe context)
  val safeIdentity: Set[String] = Set(
    "Completion",
    "NormalCompletion",
  )

  // AO(x) reduces to x (unsafe context only)
  val unsafeIdentity: Set[String] = Set(
    "ToString",
    "ToObject",
    "RequireObjectCoercible",
    "ToPropertyKey",
  )

  // AO(x) reduces to delegate(x) (unsafe context only)
  val unsafeDeleg: Map[String, String] = Map(
    "ToIntegerOrInfinity" -> "ToNumber",
    "ToLength" -> "ToIntegerOrInfinity",
    "ToIndex" -> "ToIntegerOrInfinity",
  )

  // ---------------------------------------------------------------------------
  // Formula rewriting
  // ---------------------------------------------------------------------------

  def rewriteFormula(f: Formula): List[Formula] =
    rewriteCompletion(f).map(rewriteValue)

  private def rewriteCompletion(f: Formula): List[Formula] = f match
    // table: predicate bool → type
    case FEq(SEApp(name: String, List(x)), SELit(EBool(b)))
        if predicateType.contains(name) =>
      val eq = FEq(SETypeOf(x), SEType(predicateType(name)))
      List(if (b) eq else FNot(eq))

    // special: IsRegExp
    case FEq(SEApp("IsRegExp", List(x)), SELit(EBool(true))) =>
      List(
        FEq(SETypeOf(x), SEType(ObjectT)),
        FExists(x, SELit(EStr("RegExpMatcher"))),
      )
    case FEq(SEApp("IsRegExp", List(x)), SELit(EBool(false))) =>
      List()
    case FEq(SETypeOf(SEApp("IsRegExp", _)), SEType(ty)) if ty <= NormalT =>
      List()

    // table: AO completion → type condition (Abrupt/Normal)
    case FEq(SETypeOf(SEApp(name: String, List(x))), SEType(ty))
        if abruptCond.contains(name) && (ty <= AbruptT || ty <= NormalT) =>
      val eq = FEq(SETypeOf(x), SEType(abruptCond(name)))
      if (ty <= AbruptT) List(eq) else List(FNot(eq))

    // table: inverse — Normal when typeof(x) matches condTy
    case FEq(SETypeOf(SEApp(name: String, List(x))), SEType(ty))
        if normalCond.contains(name) && (ty <= AbruptT || ty <= NormalT) =>
      val eq = FEq(SETypeOf(x), SEType(normalCond(name)))
      if (ty <= NormalT) List(eq) else List(FNot(eq))

    // special: RequireObjectCoercible passthrough (non-Abrupt/Normal ty)
    case FEq(SETypeOf(SEApp("RequireObjectCoercible", List(x))), SEType(ty)) =>
      List(FEq(SETypeOf(x), SEType(ty)))

    // special: RequireInternalSlot
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

    // table: always-normal AOs
    case FEq(SETypeOf(SEApp(name: String, _)), SEType(ty))
        if ty <= NormalT && alwaysNormal.contains(name) =>
      List()

    // table: completion delegation
    case FEq(SETypeOf(SEApp(name: String, List(x))), SEType(ty))
        if completionDeleg.contains(name) && (ty <= AbruptT || ty <= NormalT) =>
      List(FEq(SETypeOf(SEApp(completionDeleg(name), List(x))), SEType(ty)))

    // special: negated RequireInternalSlot abrupt
    case FNot(
          FEq(
            SETypeOf(SEApp("RequireInternalSlot", List(x, SELit(EStr(slot))))),
            SEType(ty),
          ),
        ) if ty <= AbruptT =>
      List(FEq(SETypeOf(x), SEType(ObjectT)), FExists(x, SELit(EStr(slot))))

    // ToNumber value-level unwrap (eq/lt, symmetric, negated)
    case FEq(SEApp("ToNumber", List(x)), v) =>
      List(FEq(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FEq(v, SEApp("ToNumber", List(x))) =>
      List(FEq(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FLt(SEApp("ToNumber", List(x)), v) =>
      List(FLt(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FLt(v, SEApp("ToNumber", List(x))) =>
      List(FLt(v, x), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FEq(SEApp("ToNumber", List(x)), v)) =>
      List(FNot(FEq(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FEq(v, SEApp("ToNumber", List(x)))) =>
      List(FNot(FEq(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FLt(SEApp("ToNumber", List(x)), v)) =>
      List(FNot(FLt(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FLt(v, SEApp("ToNumber", List(x)))) =>
      List(FNot(FLt(v, x)), FEq(SETypeOf(x), SEType(NumberT)))

    // SameValue / SameValueZero → equality
    case FEq(
          SEApp("SameValue" | "SameValueZero", List(x, y)),
          SELit(EBool(b)),
        ) =>
      if (b) List(FEq(x, y)) else List(FNot(FEq(x, y)))
    case FEq(
          SELit(EBool(b)),
          SEApp("SameValue" | "SameValueZero", List(x, y)),
        ) =>
      if (b) List(FEq(x, y)) else List(FNot(FEq(x, y)))

    // ToBoolean(x) = b → x = b (produce simplest truthy/falsy witness)
    case FEq(SEApp("ToBoolean", List(x)), SELit(EBool(b))) =>
      List(FEq(x, SELit(EBool(b))))
    case FEq(SELit(EBool(b)), SEApp("ToBoolean", List(x))) =>
      List(FEq(x, SELit(EBool(b))))

    // negation passthrough
    case FNot(inner) =>
      rewriteCompletion(inner) match
        case List(r) if r != inner => List(FNot(r))
        case _                     => List(f)

    case _ => List(f)

  // ---------------------------------------------------------------------------
  // Value-level expression reduction
  // ---------------------------------------------------------------------------

  private def rewriteValue(f: Formula): Formula = f match
    case FEq(SEProj(base, SELit(EStr("Type"))), SELit(EEnum(e))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(reduceExpr(base, safe = true)), SEType(ty))
    case FEq(SELit(EEnum(e)), SEProj(base, SELit(EStr("Type")))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(reduceExpr(base, safe = true)), SEType(ty))
    case FNot(inner)   => FNot(rewriteValue(inner))
    case FEq(l, r)     => FEq(reduceExpr(l), reduceExpr(r))
    case FLt(l, r)     => FLt(reduceExpr(l), reduceExpr(r))
    case FExists(b, k) => FExists(reduceExpr(b), k)

  private def reduceExpr(t: SymExpr, safe: Boolean = false): SymExpr = t match
    case SEApp(name: String, List(x)) if safeIdentity.contains(name) =>
      reduceExpr(x, safe)
    case SEApp("LengthOfArrayLike", List(x)) =>
      SEApp("Get", List(reduceExpr(x, safe), SELit(EStr("length"))))
    case SEApp("GetMethod", List(v, SELit(EStr(p)))) =>
      SEApp("Get", List(reduceExpr(v, safe), SELit(EStr(p))))
    case SEApp("GetMethod", List(v, SEProj(_, p))) =>
      SEApp("Get", List(reduceExpr(v, safe), p))
    case SEApp("__CLAMP__", List(x, _, _)) =>
      reduceExpr(x, safe)
    case SEApp(name: String, List(x)) if unsafeIdentity.contains(name) =>
      reduceExpr(x, safe)
    case SEApp(name: String, List(x)) if unsafeDeleg.contains(name) =>
      SEApp(unsafeDeleg(name), List(reduceExpr(x, safe)))
    case SETypeOf(inner) => SETypeOf(reduceExpr(inner, safe = true))
    case SEProj(inner, SELit(EStr("Value"))) => reduceExpr(inner, safe)
    case SEProj(base, k) => SEProj(reduceExpr(base, safe), k)
    case SEApp(op, args) => SEApp(op, args.map(reduceExpr(_, safe)))
    case SEList(elems)   => SEList(elems.map(reduceExpr(_, safe)))
    case _               => t
