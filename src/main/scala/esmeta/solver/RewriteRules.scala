package esmeta.solver

import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*

object RewriteRules {
  def rewriteFormula(f: Formula): List[Formula] =
    rewrite(stripCompletion(f)).map(normalizeExpr)

  private def rewrite(f: Formula): List[Formula] = f match
    // 7.1 Type Conversion

    // https://tc39.es/ecma262/#sec-toboolean
    case FEq(SEApp("ToBoolean", List(x)), SELit(EBool(b))) =>
      x match
        case SELit(EBool(b)) => List(FEq(x, SELit(EBool(b))))
        case SELit(lit) =>
          val isFalsy = lit match
            case EUndef() | ENull() => true
            case ENumber(d)         => d == 0.0 || d.isNaN
            case EBigInt(n)         => n == BigInt(0)
            case EStr(s)            => s.isEmpty
            case _                  => false
          if (isFalsy) List(FEq(x, SELit(EBool(false))))
          else List(FEq(x, SELit(EBool(true))))
        case _ => List(f)

    // https://tc39.es/ecma262/#sec-tonumber
    // NOTE: only handles non-object case; object case not modeled (delegate to ToPrimitive)
    case FEq(SETypeOf(SEApp("ToNumber", List(x))), SEType(ty)) if ty <= CompT =>
      val guard = FNot(FEq(SETypeOf(x), SEType(ObjectT)))
      val isSymbolOrBigInt = FEq(SETypeOf(x), SEType(SymbolT || BigIntT))
      ty match
        case _ if ty <= NormalT => List(guard, FNot(isSymbolOrBigInt))
        case _ if ty <= AbruptT => List(guard, isSymbolOrBigInt)
        case _                  => List(f)

    // FIXME: After application, return value should be treated as number
    // but in this model, we cannot handle that behavior
    // so we have to rewrite while symbolic interpretation and update environment accordingly
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

    // https://tc39.es/ecma262/#sec-tointegerorinfinity
    // NOTE: delegates to ToNumber
    case FEq(SETypeOf(SEApp("ToIntegerOrInfinity", List(x))), SEType(ty))
        if ty <= CompT =>
      val toNumber = SEApp("ToNumber", List(x))
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(FEq(SETypeOf(toNumber), SEType(ty)))
        case _ => List(f)

    // https://tc39.es/ecma262/#sec-tobigint
    // NOTE: only handles non-object case; object case not modeled (delegate to ToPrimitive)
    case FEq(SETypeOf(SEApp("ToBigInt", List(x))), SEType(ty)) if ty <= CompT =>
      val guard = FNot(FEq(SETypeOf(x), SEType(ObjectT)))
      val isThrowTy =
        FEq(SETypeOf(x), SEType(UndefT || NullT || NumberT || SymbolT))
      ty match
        case _ if ty <= NormalT => List(guard, FNot(isThrowTy))
        case _ if ty <= AbruptT => List(guard, isThrowTy)
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-tostring
    // NOTE: only handles non-object case; object case not modeled (delegate to ToPrimitive)
    case FEq(SETypeOf(SEApp("ToString", List(x))), SEType(ty)) if ty <= CompT =>
      val guard = FNot(FEq(SETypeOf(x), SEType(ObjectT)))
      val isSymbol = FEq(SETypeOf(x), SEType(SymbolT))
      ty match
        case _ if ty <= NormalT => List(guard, FNot(isSymbol))
        case _ if ty <= AbruptT => List(guard, isSymbol)
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-toobject
    case FEq(SETypeOf(SEApp("ToObject", List(x))), SEType(ty)) if ty <= CompT =>
      val isUndefOrNull = FEq(SETypeOf(x), SEType(UndefT || NullT))
      ty match
        case _ if ty <= NormalT => List(FNot(isUndefOrNull))
        case _ if ty <= AbruptT => List(isUndefOrNull)
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-tolength
    // NOTE: delegates to ToIntegerOrInfinity
    case FEq(SETypeOf(SEApp("ToLength", List(x))), SEType(ty)) if ty <= CompT =>
      val toIntegerOrInfinity = SEApp("ToIntegerOrInfinity", List(x))
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(FEq(SETypeOf(toIntegerOrInfinity), SEType(ty)))
        case _ => List(f)

    // https://tc39.es/ecma262/#sec-toindex
    // NOTE: delegates to ToIntegerOrInfinity
    case FEq(SETypeOf(SEApp("ToIndex", List(x))), SEType(ty)) if ty <= CompT =>
      val toIntegerOrInfinity = SEApp("ToIntegerOrInfinity", List(x))
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(FEq(SETypeOf(toIntegerOrInfinity), SEType(ty)))
        case _ => List(f)

    // 7.2 Testing and Comparison Operations

    // https://tc39.es/ecma262/#sec-requireobjectcoercible
    case FEq(SETypeOf(SEApp("RequireObjectCoercible", List(x))), SEType(ty))
        if ty <= CompT =>
      val isUndefOrNull = FEq(SETypeOf(x), SEType(UndefT || NullT))
      ty match
        case _ if ty <= NormalT => List(FNot(isUndefOrNull))
        case _ if ty <= AbruptT => List(isUndefOrNull)
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-isarray
    // NOTE: IsArray returns true if array exotic object, and false in non-object
    // Proxy exotic objects should be considered (according to the spec), but chose simple path now
    case FEq(SEApp("IsArray", List(x)), SELit(EBool(b))) =>
      if (b) List(FEq(SETypeOf(x), SEType(RecordT("Array"))))
      else List(FNot(FEq(SETypeOf(x), SEType(ObjectT))))

    // https://tc39.es/ecma262/#sec-iscallable
    case FEq(SEApp("IsCallable", List(x)), SELit(EBool(b))) =>
      val eq = FEq(SETypeOf(x), SEType(FunctionT))
      List(if (b) eq else FNot(eq))

    // https://tc39.es/ecma262/#sec-isconstructor
    case FEq(SEApp("IsConstructor", List(x)), SELit(EBool(b))) =>
      val eq = FEq(SETypeOf(x), SEType(ConstructorT))
      List(if (b) eq else FNot(eq))

    // https://tc39.es/ecma262/#sec-isregexp
    // NOTE: IsRegExp returns true if has [[RegExpMatcher]], and false if non-object
    // @@match check should be considered, but chose simple path now
    case FEq(SEApp("IsRegExp", List(x)), SELit(EBool(b))) =>
      if (b)
        List(
          FEq(SETypeOf(x), SEType(ObjectT)),
          FExists(x, SELit(EStr("RegExpMatcher"))),
        )
      else List(FNot(FEq(SETypeOf(x), SEType(ObjectT))))

    // https://tc39.es/ecma262/#sec-samevalue
    // NOTE: strict - +0 != -0, NaN == NaN
    case FEq(SEApp("SameValue", List(x, y)), SELit(EBool(b))) =>
      if (b) List(FEq(x, y)) else List(FNot(FEq(x, y)))
    case FEq(SELit(EBool(b)), SEApp("SameValue", List(x, y))) =>
      if (b) List(FEq(x, y)) else List(FNot(FEq(x, y)))

    // https://tc39.es/ecma262/#sec-samevaluezero
    // NOTE: lenient - +0 == -0, NaN == NaN
    case FEq(SEApp("SameValueZero", List(x, y)), SELit(EBool(b))) =>
      if (b) List(FEq(x, y)) else List(FNot(FEq(x, y)))
    case FEq(SELit(EBool(b)), SEApp("SameValueZero", List(x, y))) =>
      if (b) List(FEq(x, y)) else List(FNot(FEq(x, y)))

    // 9 Executable Code and Execution Contexts

    // https://tc39.es/ecma262/#sec-canbeheldweakly
    case FEq(SEApp("CanBeHeldWeakly", List(x)), SELit(EBool(b))) =>
      if (b) List(FEq(SETypeOf(x), SEType(ObjectT)))
      else
        List(
          FNot(FEq(SETypeOf(x), SEType(ObjectT))),
          FNot(FEq(SETypeOf(x), SEType(SymbolT))),
        )

    // 10.1 Ordinary Object Internal Methods and Internal Slots

    // https://tc39.es/ecma262/#sec-requireinternalslot
    case FEq(
          SETypeOf(SEApp("RequireInternalSlot", List(x, SELit(EStr(slot))))),
          SEType(ty),
        ) if ty <= CompT =>
      ty match
        case _ if ty <= NormalT =>
          List(FEq(SETypeOf(x), SEType(ObjectT)), FExists(x, SELit(EStr(slot))))
        case _ if ty <= AbruptT => List(FNot(FEq(SETypeOf(x), SEType(ObjectT))))
        case _                  => List(f)

    // ThisXXXValue series (around 20.XX)

    // https://tc39.es/ecma262/#sec-thissymbolvalue
    case FEq(SETypeOf(SEApp("ThisSymbolValue", List(x))), SEType(ty))
        if ty <= CompT =>
      val isSymbol = FEq(SETypeOf(x), SEType(SymbolT))
      ty match
        case _ if ty <= NormalT => List(isSymbol)
        case _ if ty <= AbruptT => List(FNot(isSymbol))
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-thisnumbervalue
    case FEq(SETypeOf(SEApp("ThisNumberValue", List(x))), SEType(ty))
        if ty <= CompT =>
      val isNumber = FEq(SETypeOf(x), SEType(NumberT))
      ty match
        case _ if ty <= NormalT => List(isNumber)
        case _ if ty <= AbruptT => List(FNot(isNumber))
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-thisbigintvalue
    case FEq(SETypeOf(SEApp("ThisBigIntValue", List(x))), SEType(ty))
        if ty <= CompT =>
      val isBigInt = FEq(SETypeOf(x), SEType(BigIntT))
      ty match
        case _ if ty <= NormalT => List(isBigInt)
        case _ if ty <= AbruptT => List(FNot(isBigInt))
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-thisstringvalue
    case FEq(SETypeOf(SEApp("ThisStringValue", List(x))), SEType(ty))
        if ty <= CompT =>
      val isString = FEq(SETypeOf(x), SEType(StrT))
      ty match
        case _ if ty <= NormalT => List(isString)
        case _ if ty <= AbruptT => List(FNot(isString))
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-thisbooleanvalue
    case FEq(SETypeOf(SEApp("ThisBooleanValue", List(x))), SEType(ty))
        if ty <= CompT =>
      val isBoolean = FEq(SETypeOf(x), SEType(BoolT))
      ty match
        case _ if ty <= NormalT => List(isBoolean)
        case _ if ty <= AbruptT => List(FNot(isBoolean))
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-ordinarycreatefromconstructor
    // NOTE: delegates to Get(constructor, "prototype") via GetPrototypeFromConstructor
    case FEq(
          SETypeOf(SEApp("OrdinaryCreateFromConstructor", List(ctor, _*))),
          SEType(ty),
        ) if ty <= CompT =>
      val getProto = SEApp("Get", List(ctor, SELit(EStr("prototype"))))
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(FEq(SETypeOf(getProto), SEType(ty)))
        case _ => List(f)

    // https://tc39.es/ecma262/#sec-installerrorcause
    // NOTE: delegates to HasProperty(options, "cause")
    case FEq(
          SETypeOf(SEApp("InstallErrorCause", List(_, options))),
          SEType(ty),
        ) if ty <= CompT =>
      val hasCause = SEApp("HasProperty", List(options, SELit(EStr("cause"))))
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(FEq(SETypeOf(hasCause), SEType(ty)))
        case _ => List(f)

    case _ => List(f)

  // strips .Value, Completion/NormalCompletion, .Type (before rewrite)

  private def stripCompletion(f: Formula): Formula = f match
    case FEq(SEProj(base, SELit(EStr("Type"))), SELit(EEnum(e))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(stripExpr(base)), SEType(ty))
    case FEq(SELit(EEnum(e)), SEProj(base, SELit(EStr("Type")))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(stripExpr(base)), SEType(ty))
    case FNot(inner)   => FNot(stripCompletion(inner))
    case FEq(l, r)     => FEq(stripExpr(l), stripExpr(r))
    case FLt(l, r)     => FLt(stripExpr(l), stripExpr(r))
    case FExists(b, k) => FExists(stripExpr(b), k)

  private def stripExpr(t: SymExpr): SymExpr = t match
    case SEApp("Completion", List(x))        => stripExpr(x)
    case SEApp("NormalCompletion", List(x))  => stripExpr(x)
    case SEProj(inner, SELit(EStr("Value"))) => stripExpr(inner)
    case SETypeOf(inner)                     => SETypeOf(stripExpr(inner))
    case SEProj(base, k)                     => SEProj(stripExpr(base), k)
    case SEApp(op, args)                     => SEApp(op, args.map(stripExpr))
    case SEList(elems)                       => SEList(elems.map(stripExpr))
    case _                                   => t

  // strips AO wrappers for value-level witness generation (after rewrite)

  private def normalizeExpr(f: Formula): Formula = f match
    case FEq(SEProj(base, SELit(EStr("Type"))), SELit(EEnum(e))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(reduceExpr(base)), SEType(ty))
    case FEq(SELit(EEnum(e)), SEProj(base, SELit(EStr("Type")))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(reduceExpr(base)), SEType(ty))
    case FNot(inner)   => FNot(normalizeExpr(inner))
    case FEq(l, r)     => FEq(reduceExpr(l), reduceExpr(r))
    case FLt(l, r)     => FLt(reduceExpr(l), reduceExpr(r))
    case FExists(b, k) => FExists(reduceExpr(b), k)

  private def reduceExpr(t: SymExpr): SymExpr = t match
    case SEApp("Completion", List(x))       => reduceExpr(x)
    case SEApp("NormalCompletion", List(x)) => reduceExpr(x)
    case SEApp("LengthOfArrayLike", List(x)) =>
      SEApp("Get", List(reduceExpr(x), SELit(EStr("length"))))
    case SEApp("GetMethod", List(v, SELit(EStr(p)))) =>
      SEApp("Get", List(reduceExpr(v), SELit(EStr(p))))
    case SEApp("GetMethod", List(v, SEProj(_, p))) =>
      SEApp("Get", List(reduceExpr(v), p))
    case SEApp("__CLAMP__", List(x, _, _))        => reduceExpr(x)
    case SEApp("ToString", List(x))               => reduceExpr(x)
    case SEApp("ToObject", List(x))               => reduceExpr(x)
    case SEApp("RequireObjectCoercible", List(x)) => reduceExpr(x)
    case SEApp("ToPropertyKey", List(x))          => reduceExpr(x)
    case SEApp("ToIntegerOrInfinity", List(x)) =>
      SEApp("ToNumber", List(reduceExpr(x)))
    case SEApp("ToLength", List(x)) =>
      SEApp("ToIntegerOrInfinity", List(reduceExpr(x)))
    case SEApp("ToIndex", List(x)) =>
      SEApp("ToIntegerOrInfinity", List(reduceExpr(x)))
    case SETypeOf(inner)                     => SETypeOf(reduceExpr(inner))
    case SEProj(inner, SELit(EStr("Value"))) => reduceExpr(inner)
    case SEProj(base, k)                     => SEProj(reduceExpr(base), k)
    case SEApp(op, args) => SEApp(op, args.map(reduceExpr(_)))
    case SEList(elems)   => SEList(elems.map(reduceExpr(_)))
    case _               => t
}
