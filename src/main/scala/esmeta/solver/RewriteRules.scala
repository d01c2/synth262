package esmeta.solver

import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*

object RewriteRules {
  def rewriteFormula(f: Formula): List[Formula] =
    rewrite(stripCompletion(f)).map(normalizeExpr)

  private val ValueKey = SELit(EStr("Value"))
  private val TypeKey = SELit(EStr("Type"))
  private val Contradiction = FEq(SELit(EBool(true)), SELit(EBool(false)))

  private def rewrite(f: Formula): List[Formula] = f match
    // Completion record wrappers
    case FEq(SETypeOf(SEApp("NormalCompletion", List(x))), SEType(ty))
        if ty <= CompT =>
      if (ty <= AbruptT) List(Contradiction)
      else normalCompletionTypeConstraints(x, ty)
    case FEq(SETypeOf(SEApp("Completion", List(x))), SEType(ty))
        if ty <= CompT && isKnownCompletionExpr(x) =>
      List(FEq(SETypeOf(x), SEType(ty)))

    // 7.1 Type Conversion

    // https://tc39.es/ecma262/#sec-toboolean
    case FEq(SEApp("ToBoolean", List(x)), SELit(EBool(expected))) =>
      x match
        case SELit(_: EBool) => List(FEq(x, SELit(EBool(expected))))
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
    case FEq(
          SETypeOf(SEProj(SEApp("ToNumber", List(x)), SELit(EStr("Value")))),
          SEType(ty),
        ) if ty <= NumberT =>
      List(FEq(SETypeOf(x), SEType(ty)))
    case FNot(
          FEq(
            SETypeOf(SEProj(SEApp("ToNumber", List(x)), SELit(EStr("Value")))),
            SEType(ty),
          ),
        ) if ty <= NumberT =>
      List(
        FNot(FEq(SETypeOf(x), SEType(ty))),
        FEq(SETypeOf(x), SEType(NumberT)),
      )

    // FIXME: After application, return value should be treated as number
    // but in this model, we cannot handle that behavior
    // so we have to rewrite while symbolic interpretation and update environment accordingly
    case FEq(SEApp("ToNumber", List(x)), v) =>
      List(FEq(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FEq(v, SEApp("ToNumber", List(x))) =>
      List(FEq(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FEq(SEProj(SEApp("ToNumber", List(x)), SELit(EStr("Value"))), v) =>
      List(FEq(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FEq(v, SEProj(SEApp("ToNumber", List(x)), SELit(EStr("Value")))) =>
      List(FEq(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FLt(SEApp("ToNumber", List(x)), v) =>
      List(FLt(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FLt(v, SEApp("ToNumber", List(x))) =>
      List(FLt(v, x), FEq(SETypeOf(x), SEType(NumberT)))
    case FLt(SEProj(SEApp("ToNumber", List(x)), SELit(EStr("Value"))), v) =>
      List(FLt(x, v), FEq(SETypeOf(x), SEType(NumberT)))
    case FLt(v, SEProj(SEApp("ToNumber", List(x)), SELit(EStr("Value")))) =>
      List(FLt(v, x), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FEq(SEApp("ToNumber", List(x)), v)) =>
      List(FNot(FEq(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FEq(v, SEApp("ToNumber", List(x)))) =>
      List(FNot(FEq(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(
          FEq(SEProj(SEApp("ToNumber", List(x)), SELit(EStr("Value"))), v),
        ) =>
      List(FNot(FEq(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(
          FEq(v, SEProj(SEApp("ToNumber", List(x)), SELit(EStr("Value")))),
        ) =>
      List(FNot(FEq(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FLt(SEApp("ToNumber", List(x)), v)) =>
      List(FNot(FLt(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(FLt(v, SEApp("ToNumber", List(x)))) =>
      List(FNot(FLt(v, x)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(
          FLt(SEProj(SEApp("ToNumber", List(x)), SELit(EStr("Value"))), v),
        ) =>
      List(FNot(FLt(x, v)), FEq(SETypeOf(x), SEType(NumberT)))
    case FNot(
          FLt(v, SEProj(SEApp("ToNumber", List(x)), SELit(EStr("Value")))),
        ) =>
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
        case _ if ty <= NormalT => List(FNot(isSymbol))
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
    // NOTE: true for Array exotic, false otherwise; Proxy recurses via ValidateNonRevokedProxy
    case FEq(SEApp("IsArray", List(x)), SELit(EBool(b))) =>
      if (b) List(FEq(SETypeOf(x), SEType(RecordT("Array"))))
      else List(FNot(FEq(SETypeOf(x), SEType(RecordT("Array")))))
    case FEq(SETypeOf(SEApp("IsArray", List(x))), SEType(ty)) if ty <= CompT =>
      ty match
        case _ if ty <= NormalT =>
          List(FNot(FEq(SETypeOf(x), SEType(RecordT("ProxyExoticObject")))))
        case _ if ty <= AbruptT =>
          List(
            FEq(SETypeOf(SEApp("ValidateNonRevokedProxy", List(x))), SEType(ty)),
          )
        case _ => List(f)

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
    case FEq(SETypeOf(SEApp("IsRegExp", List(x))), SEType(ty)) if ty <= CompT =>
      val symMatch = SEProj(SEApp("SYMBOL", List()), SELit(EStr("match")))
      val getMatch = SEApp("Get", List(x, symMatch))
      ty match
        case _ if ty <= NormalT => List()
        case _ if ty <= AbruptT =>
          List(
            FEq(SETypeOf(x), SEType(ObjectT)),
            FEq(SETypeOf(getMatch), SEType(ty)),
          )
        case _ => List(f)

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

    // https://tc39.es/ecma262/#sec-validatenonrevokedproxy
    // NOTE: throws TypeError only if proxy is revoked (handler is null)
    case FEq(
          SETypeOf(SEApp("ValidateNonRevokedProxy", List(o))),
          SEType(ty),
        ) if ty <= CompT =>
      val hasHandler = FExists(o, SELit(EStr("ProxyHandler")))
      ty match
        case _ if ty <= NormalT => List(hasHandler)
        case _ if ty <= AbruptT => List(FNot(hasHandler))
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-validatetypedarray
    // NOTE: delegates to RequireInternalSlot(typedArray, "TypedArrayName")
    case FEq(
          SETypeOf(SEApp("ValidateTypedArray", List(o, _))),
          SEType(ty),
        ) if ty <= CompT =>
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(
            FEq(
              SETypeOf(
                SEApp(
                  "RequireInternalSlot",
                  List(o, SELit(EStr("TypedArrayName"))),
                ),
              ),
              SEType(ty),
            ),
          )
        case _ => List(f)

    // 27.1 Iteration

    // https://tc39.es/ecma262/#sec-getiterator
    case FEq(SETypeOf(SEApp("GetIterator", List(obj))), SEType(ty))
        if ty <= NormalT =>
      val methodResult = SEApp("Get", List(obj, SELit(EStr("iterator"))))
      val method = SEProj(methodResult, SELit(EStr("Value")))
      val callResult = SEApp("Call", List(method, obj))
      List(
        FEq(SETypeOf(methodResult), SEType(NormalT)),
        FEq(SETypeOf(callResult), SEType(NormalT)),
        FEq(SETypeOf(SEProj(callResult, SELit(EStr("Value")))), SEType(ObjectT)),
      )

    // https://tc39.es/ecma262/#sec-getiteratorfrommethod
    case FEq(
          SETypeOf(SEApp("GetIteratorFromMethod", List(obj, method))),
          SEType(ty),
        ) if ty <= NormalT =>
      val callResult = SEApp("Call", List(method, obj))
      List(
        FEq(SETypeOf(callResult), SEType(NormalT)),
        FEq(SETypeOf(SEProj(callResult, SELit(EStr("Value")))), SEType(ObjectT)),
      )

    // https://tc39.es/ecma262/#sec-iteratornext
    case FEq(SETypeOf(SEApp("IteratorNext", iterRecord :: args)), SEType(ty))
        if ty <= NormalT =>
      iteratorParts(iterRecord) match
        case Some(_) =>
          val result = iteratorNextResult(iterRecord, args)
          List(
            FEq(SETypeOf(result), SEType(NormalT)),
            FEq(
              SETypeOf(SEProj(result, SELit(EStr("Value")))),
              SEType(ObjectT),
            ),
          )
        case None => List(f)

    // https://tc39.es/ecma262/#sec-iteratorcomplete
    case FEq(SETypeOf(SEApp("IteratorComplete", List(result))), SEType(ty))
        if ty <= NormalT =>
      val doneResult =
        SEApp("Get", List(iteratorResultValue(result), SELit(EStr("done"))))
      List(
        FEq(SETypeOf(doneResult), SEType(NormalT)),
        FEq(SETypeOf(SEProj(doneResult, SELit(EStr("Value")))), SEType(BoolT)),
      )

    // https://tc39.es/ecma262/#sec-iteratorvalue
    case FEq(SETypeOf(SEApp("IteratorValue", List(result))), SEType(ty))
        if ty <= NormalT =>
      val valueResult =
        SEApp("Get", List(iteratorResultValue(result), SELit(EStr("value"))))
      List(FEq(SETypeOf(valueResult), SEType(NormalT)))

    case _ => rewriteCompletionValues(f).getOrElse(f) :: Nil

  // Converts .Type comparisons before rewrite while preserving completion
  // wrappers whose value semantics need explicit rewrite rules.

  private def stripCompletion(f: Formula): Formula = f match
    case FEq(SEProj(base, TypeKey), SELit(EEnum(e))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(stripExpr(base)), SEType(ty))
    case FEq(SELit(EEnum(e)), SEProj(base, TypeKey)) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(stripExpr(base)), SEType(ty))
    case FNot(inner)   => FNot(stripCompletion(inner))
    case FEq(l, r)     => FEq(stripExpr(l), stripExpr(r))
    case FLt(l, r)     => FLt(stripExpr(l), stripExpr(r))
    case FExists(b, k) => FExists(stripExpr(b), k)

  private def stripExpr(t: SymExpr): SymExpr = t match
    case SETypeOf(inner) => SETypeOf(stripExpr(inner))
    case SEProj(base, k) => SEProj(stripExpr(base), stripExpr(k))
    case SEApp(op, args) => SEApp(op, args.map(stripExpr))
    case SEList(elems)   => SEList(elems.map(stripExpr))
    case SERecord(tn, fields) =>
      SERecord(tn, fields.map((k, v) => k -> stripExpr(v)))
    case SEMap(entries) =>
      SEMap(entries.map((k, v) => stripExpr(k) -> stripExpr(v)))
    case _ => t

  // Normalizes value-level AO projections after rewrite.

  private def normalizeExpr(f: Formula): Formula = f match
    case FEq(SEProj(base, TypeKey), SELit(EEnum(e))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(reduceExpr(base)), SEType(ty))
    case FEq(SELit(EEnum(e)), SEProj(base, TypeKey)) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FEq(SETypeOf(reduceExpr(base)), SEType(ty))
    case FNot(inner)   => FNot(normalizeExpr(inner))
    case FEq(l, r)     => FEq(reduceExpr(l), reduceExpr(r))
    case FLt(l, r)     => FLt(reduceExpr(l), reduceExpr(r))
    case FExists(b, k) => FExists(reduceExpr(b), k)

  private def reduceExpr(t: SymExpr): SymExpr = t match
    case SEProj(SEApp("ToIntegerOrInfinity", List(x)), ValueKey) =>
      SEProj(SEApp("ToNumber", List(reduceExpr(x))), ValueKey)
    case SEProj(SEApp("ToLength", List(x)), ValueKey) =>
      SEProj(SEApp("ToNumber", List(reduceExpr(x))), ValueKey)
    case SEProj(SEApp("ToIndex", List(x)), ValueKey) =>
      SEProj(SEApp("ToNumber", List(reduceExpr(x))), ValueKey)
    case SEProj(SEApp("ToString", List(x)), ValueKey) =>
      reduceExpr(x)
    case SEProj(SEApp("ToObject", List(x)), ValueKey) =>
      reduceExpr(x)
    case SEProj(
          SEApp("RequireObjectCoercible", List(x)),
          ValueKey,
        ) =>
      reduceExpr(x)
    case SEProj(SEApp("ToPropertyKey", List(x)), ValueKey) =>
      reduceExpr(x)
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
    case SETypeOf(inner)         => SETypeOf(reduceExpr(inner))
    case SEProj(inner, ValueKey) => SEProj(reduceExpr(inner), ValueKey)
    case SEProj(base, k)         => SEProj(reduceExpr(base), reduceExpr(k))
    case SEApp(op, args)         => SEApp(op, args.map(reduceExpr(_)))
    case SEList(elems)           => SEList(elems.map(reduceExpr(_)))
    case SERecord(tn, fields) =>
      SERecord(tn, fields.map((k, v) => k -> reduceExpr(v)))
    case SEMap(entries) =>
      SEMap(entries.map((k, v) => reduceExpr(k) -> reduceExpr(v)))
    case _ => t

  private def rewriteCompletionValues(f: Formula): Option[Formula] = f match
    case FNot(inner) =>
      rewriteCompletionValues(inner).map(FNot(_))
    case FEq(l, r) =>
      rewriteCompletionValueExpr(l)
        .map(FEq(_, r))
        .orElse(rewriteCompletionValueExpr(r).map(FEq(l, _)))
    case FLt(l, r) =>
      rewriteCompletionValueExpr(l)
        .map(FLt(_, r))
        .orElse(rewriteCompletionValueExpr(r).map(FLt(l, _)))
    case FExists(b, k) =>
      rewriteCompletionValueExpr(b).map(FExists(_, k))

  private def rewriteCompletionValueExpr(expr: SymExpr): Option[SymExpr] =
    expr match
      case SEProj(SEApp("NormalCompletion", List(inner)), ValueKey) =>
        Some(reduceExpr(inner))
      case SEProj(SEApp("Completion", List(inner)), ValueKey)
          if isKnownCompletionExpr(inner) =>
        Some(SEProj(reduceExpr(inner), ValueKey))
      case SETypeOf(inner) =>
        rewriteCompletionValueExpr(inner).map(SETypeOf(_))
      case SEProj(base, key) =>
        rewriteCompletionValueExpr(base)
          .map(SEProj(_, key))
          .orElse(rewriteCompletionValueExpr(key).map(SEProj(base, _)))
      case SEApp(op, args) =>
        rewriteFirst(args, rewriteCompletionValueExpr).map(SEApp(op, _))
      case SEList(elems) =>
        rewriteFirst(elems, rewriteCompletionValueExpr).map(SEList(_))
      case SERecord(tn, fields) =>
        rewriteFirstMapValue(fields, rewriteCompletionValueExpr)
          .map(SERecord(tn, _))
      case SEMap(entries) =>
        rewriteFirst(
          entries,
          {
            case (k, v) =>
              rewriteCompletionValueExpr(k)
                .map(_ -> v)
                .orElse(rewriteCompletionValueExpr(v).map(k -> _))
          },
        ).map(SEMap(_))
      case _ => None

  private def rewriteFirst[A](
    values: List[A],
    f: A => Option[A],
  ): Option[List[A]] =
    values match
      case Nil => None
      case head :: tail =>
        f(head).map(_ :: tail).orElse(rewriteFirst(tail, f).map(head :: _))

  private def rewriteFirstMapValue(
    fields: Map[String, SymExpr],
    f: SymExpr => Option[SymExpr],
  ): Option[Map[String, SymExpr]] =
    rewriteFirst(
      fields.toList,
      {
        case (k, v) => f(v).map(k -> _)
      },
    ).map(_.toMap)

  private def normalCompletionTypeConstraints(
    value: SymExpr,
    ty: ValueTy,
  ): List[Formula] =
    val valueTy = (ty && NormalT).record("Value").value
    if (valueTy.isTop) Nil else List(FEq(SETypeOf(value), SEType(valueTy)))

  private val completionReturningOps: Set[String] = Set(
    "Call",
    "Construct",
    "DefineOwnProperty",
    "Delete",
    "Get",
    "GetIterator",
    "GetIteratorFromMethod",
    "GetMethod",
    "GetOwnProperty",
    "GetPrototypeOf",
    "GetV",
    "HasProperty",
    "InstallErrorCause",
    "IsArray",
    "IsExtensible",
    "IsRegExp",
    "IteratorComplete",
    "IteratorNext",
    "IteratorValue",
    "OrdinaryCreateFromConstructor",
    "OwnPropertyKeys",
    "PreventExtensions",
    "RequireInternalSlot",
    "RequireObjectCoercible",
    "Set",
    "SetPrototypeOf",
    "ThisBigIntValue",
    "ThisBooleanValue",
    "ThisNumberValue",
    "ThisStringValue",
    "ThisSymbolValue",
    "ToBigInt",
    "ToIndex",
    "ToIntegerOrInfinity",
    "ToLength",
    "ToNumber",
    "ToObject",
    "ToString",
    "ValidateNonRevokedProxy",
    "ValidateTypedArray",
  )

  private def isKnownCompletionExpr(expr: SymExpr): Boolean = expr match
    case SEApp("Completion" | "NormalCompletion", List(_)) => true
    case SEApp(op: String, _) => completionReturningOps(op)
    case _                    => false

  private def iteratorParts(
    iterRecord: SymExpr,
  ): Option[(SymExpr, SymExpr, SymExpr)] =
    reduceExpr(iterRecord) match
      case SERecord("IteratorRecord", fields) =>
        for {
          iterator <- fields.get("Iterator")
          nextMethod <- fields.get("NextMethod")
          done <- fields.get("Done")
        } yield (reduceExpr(iterator), reduceExpr(nextMethod), reduceExpr(done))
      case _ => None

  private def iteratorNextResult(
    iterRecord: SymExpr,
    args: List[SymExpr],
  ): SymExpr =
    iteratorParts(iterRecord) match
      case Some((iterator, nextMethod, _)) =>
        val callArgs = List(nextMethod, iterator) ++ args.map(reduceExpr)
        SEApp("Call", callArgs)
      case None =>
        SEApp("IteratorNext", reduceExpr(iterRecord) :: args.map(reduceExpr))

  private def iteratorResultValue(result: SymExpr): SymExpr =
    reduceExpr(result) match
      case SEApp("IteratorNext", iterRecord :: args) =>
        SEProj(iteratorNextResult(iterRecord, args), SELit(EStr("Value")))
      case app @ SEApp("Call", _) => SEProj(app, SELit(EStr("Value")))
      case other                  => other
}
