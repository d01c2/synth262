package esmeta.solver

import esmeta.cfg.CFG
import esmeta.ir.*
import esmeta.ty.*
import esmeta.util.*
import Formula.*, SymExpr.*

object RewriteRules {
  def rewriteFormula(f: Formula)(using CFG): List[Formula] =
    rewrite(stripCompletion(f)).map(normalizeExpr)

  case class AoCase(when: Goal, thenF: Goal)

  def aoModel(call: SymExpr): List[AoCase] = call match
    case SEApp("ToNumber", List(x))  => toNumberModel(x, call)
    case SEApp("ToBoolean", List(x)) => toBooleanModel(x, call)
    case SEApp("ToObject", List(x))  => toObjectModel(x, call)
    case SEApp("ToBigInt", List(x))  => toBigIntModel(x, call)
    case SEApp("ToString", List(x))  => toStringModel(x, call)
    case SEApp("RequireObjectCoercible", List(x)) =>
      requireObjectCoercibleModel(x, call)
    case SEApp("ThisSymbolValue", List(x)) =>
      thisValueModel(x, call, SymbolT, "SymbolData")
    case SEApp("ThisNumberValue", List(x)) =>
      thisValueModel(x, call, NumberT, "NumberData")
    case SEApp("ThisBigIntValue", List(x)) =>
      thisValueModel(x, call, BigIntT, "BigIntData")
    case SEApp("ThisStringValue", List(x)) =>
      thisValueModel(x, call, StrT, "StringData")
    case SEApp("ThisBooleanValue", List(x)) =>
      thisValueModel(x, call, BoolT, "BooleanData")
    case SEApp("IsArray", List(x))       => isArrayModel(x, call)
    case SEApp("IsCallable", List(x))    => isCallableModel(x, call)
    case SEApp("IsConstructor", List(x)) => isConstructorModel(x, call)
    case SEApp("IsRegExp", List(x))      => isRegExpModel(x, call)
    case _                               => Nil

  def isModeledCall(expr: SymExpr): Boolean = expr match
    case SEApp("ToNumber", List(_))               => true
    case SEApp("ToBoolean", List(_))              => true
    case SEApp("ToObject", List(_))               => true
    case SEApp("ToBigInt", List(_))               => true
    case SEApp("ToString", List(_))               => true
    case SEApp("RequireObjectCoercible", List(_)) => true
    case SEApp("ThisSymbolValue", List(_))        => true
    case SEApp("ThisNumberValue", List(_))        => true
    case SEApp("ThisBigIntValue", List(_))        => true
    case SEApp("ThisStringValue", List(_))        => true
    case SEApp("ThisBooleanValue", List(_))       => true
    case SEApp("IsArray", List(_))                => true
    case SEApp("IsCallable", List(_))             => true
    case SEApp("IsConstructor", List(_))          => true
    case SEApp("IsRegExp", List(_))               => true
    case _                                        => false

  private def toBooleanModel(x: SymExpr, ret: SymExpr): List[AoCase] =
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    // return values cannot be inferred from detailed-types, so checked CFG
    List(
      AoCase(List(FTypeCheck(x, UndefT)), List(FEq(ret, f))),
      AoCase(List(FTypeCheck(x, NullT)), List(FEq(ret, f))),
      AoCase(List(FTypeCheck(x, BoolT)), List(FEq(ret, x))),
      // detailed-types has no value-level BigInt; split via CFG branch `= argument 0n`
      AoCase(
        List(FTypeCheck(x, BigIntT), FEq(x, SELit(EBigInt(BigInt(0))))),
        List(FEq(ret, f)),
      ),
      AoCase(
        List(FTypeCheck(x, BigIntT), FNot(FEq(x, SELit(EBigInt(BigInt(0)))))),
        List(FEq(ret, t)),
      ),
      AoCase(
        List(FTypeCheck(x, ValueTy(number = NumberIntTy(IntTy.Zero, true)))),
        List(FEq(ret, f)),
      ),
      AoCase(
        List(
          FTypeCheck(
            x,
            ValueTy(number = NumberSignTy(Sign.Neg || Sign.Pos, false)),
          ),
        ),
        List(FEq(ret, t)),
      ),
      AoCase(
        List(FTypeCheck(x, ValueTy(str = Fin(Set(""))))),
        List(FEq(ret, f)),
      ),
      AoCase(List(FTypeCheck(x, StrT)), List(FEq(ret, t))),
      AoCase(List(FTypeCheck(x, SymbolT)), List(FEq(ret, t))),
      AoCase(List(FTypeCheck(x, ObjectT)), List(FEq(ret, t))),
    )

  private def toObjectModel(x: SymExpr, ret: SymExpr): List[AoCase] =
    val abrupt = List(FTypeCheck(ret, ThrowT))
    val normal = List(FTypeCheck(ret, NormalT))
    // Wrapper cases return new objects whose internal fields (e.g., Prototype,
    // BooleanData) are visible in CFG but not expressible as type constraints.
    // ret.Value only constrained for Object (identity).
    List(
      AoCase(List(FTypeCheck(x, UndefT)), abrupt),
      AoCase(List(FTypeCheck(x, NullT)), abrupt),
      AoCase(List(FTypeCheck(x, BoolT)), normal),
      AoCase(List(FTypeCheck(x, NumberT)), normal),
      AoCase(List(FTypeCheck(x, StrT)), normal),
      AoCase(List(FTypeCheck(x, SymbolT)), normal),
      AoCase(List(FTypeCheck(x, BigIntT)), normal),
      AoCase(
        List(FTypeCheck(x, ObjectT)),
        List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), x)),
      ),
    )

  // Shared model for ThisSymbolValue, ThisNumberValue, ThisBigIntValue,
  // ThisStringValue, ThisBooleanValue — 5 return nodes each; 2 analysis dropped.
  private def thisValueModel(
    x: SymExpr,
    ret: SymExpr,
    primTy: ValueTy,
    slot: String,
  ): List[AoCase] =
    List(
      AoCase(
        List(FTypeCheck(x, primTy)),
        List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), x)),
      ),
      AoCase(
        List(FTypeCheck(x, ObjectT), FExists(x, SELit(EStr(slot)))),
        List(FTypeCheck(ret, NormalT)),
      ),
      AoCase(
        List(FNot(FTypeCheck(x, primTy)), FNot(FExists(x, SELit(EStr(slot))))),
        List(FTypeCheck(ret, ThrowT)),
      ),
    )

  private def isCallableModel(x: SymExpr, ret: SymExpr): List[AoCase] =
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    val hasCall = FExists(x, SELit(EStr("Call")))
    // 3 return nodes, all modeled. Returns Boolean directly (not a completion).
    // CFG checks `exists argument.Call`
    List(
      AoCase(List(FNot(FTypeCheck(x, ObjectT))), List(FEq(ret, f))),
      AoCase(List(FTypeCheck(x, ObjectT), hasCall), List(FEq(ret, t))),
      AoCase(List(FTypeCheck(x, ObjectT), FNot(hasCall)), List(FEq(ret, f))),
    )

  private def isConstructorModel(x: SymExpr, ret: SymExpr): List[AoCase] =
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    val hasConstruct = FExists(x, SELit(EStr("Construct")))
    // 3 return nodes, all modeled. Returns Boolean directly (not a completion).
    // CFG checks `exists argument.Construct`
    List(
      AoCase(List(FNot(FTypeCheck(x, ObjectT))), List(FEq(ret, f))),
      AoCase(List(FTypeCheck(x, ObjectT), hasConstruct), List(FEq(ret, t))),
      AoCase(
        List(FTypeCheck(x, ObjectT), FNot(hasConstruct)),
        List(FEq(ret, f)),
      ),
    )

  private def isRegExpModel(x: SymExpr, ret: SymExpr): List[AoCase] =
    def normal(v: SymExpr): Goal =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    val symMatch = SEProj(SEApp("SYMBOL", List()), SELit(EStr("match")))
    // 6 return nodes; dropped 2 inter-proc (1532,1537 via ToBoolean);
    // 1 analysis dropped (1530).
    // RegExpMatcher case (1535) is reachable only when Get(@@match)=undefined;
    // when condition omits this check — imprecise for @@match-overriding objects.
    List(
      AoCase(List(FNot(FTypeCheck(x, ObjectT))), normal(f)),
      AoCase(
        List(
          FTypeCheck(x, ObjectT),
          FTypeCheck(SEApp("Get", List(x, symMatch)), AbruptT),
        ),
        List(FTypeCheck(ret, ThrowT)),
      ),
      AoCase(
        List(FTypeCheck(x, ObjectT), FExists(x, SELit(EStr("RegExpMatcher")))),
        normal(t),
      ),
    )

  private def isArrayModel(x: SymExpr, ret: SymExpr): List[AoCase] =
    def normal(v: SymExpr): Goal =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    // 6 return nodes; dropped 3 inter-proc (1493,1499,1500 via
    // ValidateNonRevokedProxy/recursive IsArray on ProxyExoticObject).
    // Third case: detailed-types only knows `#0: Record[Object]` at node 1501;
    // the "not Array, not Proxy" narrowing comes from CFG control flow, not
    // from occurrence typing — detailed-types cannot express prior-branch exclusion.
    List(
      AoCase(List(FNot(FTypeCheck(x, ObjectT))), normal(f)),
      AoCase(List(FTypeCheck(x, RecordT("Array"))), normal(t)),
      AoCase( // This case cannot be inferred only from detailed-types
        List(
          FTypeCheck(x, ObjectT),
          FNot(FTypeCheck(x, RecordT("Array") || RecordT("ProxyExoticObject"))),
        ),
        normal(f),
      ),
    )

  private def requireObjectCoercibleModel(
    x: SymExpr,
    ret: SymExpr,
  ): List[AoCase] =
    // 3 return nodes, all modeled.
    List(
      AoCase(List(FTypeCheck(x, UndefT)), List(FTypeCheck(ret, ThrowT))),
      AoCase(List(FTypeCheck(x, NullT)), List(FTypeCheck(ret, ThrowT))),
      AoCase(
        List(FNot(FTypeCheck(x, UndefT || NullT))),
        List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), x)),
      ),
    )

  private def toStringModel(x: SymExpr, ret: SymExpr): List[AoCase] =
    def normal(v: SymExpr): Goal =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    // Open dependency: dropped 7 inter-proc (1412,1414,1418,1420,1425,1431,1432
    // via Number::toString/BigInt::toString/ToPrimitive); 1 analysis dropped (1390)
    // due to infeasible Completion check.
    List(
      AoCase(List(FTypeCheck(x, StrT)), normal(x)),
      AoCase(List(FTypeCheck(x, SymbolT)), List(FTypeCheck(ret, ThrowT))),
      AoCase(List(FTypeCheck(x, UndefT)), normal(SELit(EStr("undefined")))),
      AoCase(List(FTypeCheck(x, NullT)), normal(SELit(EStr("null")))),
      AoCase(List(FTypeCheck(x, TrueT)), normal(SELit(EStr("true")))),
      AoCase(List(FTypeCheck(x, FalseT)), normal(SELit(EStr("false")))),
    )

  private def toBigIntModel(x: SymExpr, ret: SymExpr): List[AoCase] =
    def normal(v: SymExpr): Goal =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    val abrupt = List(FTypeCheck(ret, ThrowT))
    // Open dependency: dropped 3 inter-proc (91,121,123 via ToPrimitive/StringToBigInt).
    // detailed-types has no value-level Boolean; split via CFG branch `if prim`
    List(
      AoCase(List(FTypeCheck(x, UndefT)), abrupt),
      AoCase(List(FTypeCheck(x, NullT)), abrupt),
      AoCase(List(FTypeCheck(x, NumberT)), abrupt),
      AoCase(List(FTypeCheck(x, SymbolT)), abrupt),
      AoCase(
        List(FTypeCheck(x, BoolT), FEq(x, SELit(EBool(true)))),
        normal(SELit(EBigInt(BigInt(1)))),
      ),
      AoCase(
        List(FTypeCheck(x, BoolT), FEq(x, SELit(EBool(false)))),
        normal(SELit(EBigInt(BigInt(0)))),
      ),
      AoCase(List(FTypeCheck(x, BigIntT)), normal(x)),
    )

  private def toNumberModel(x: SymExpr, ret: SymExpr): List[AoCase] =
    def normal(v: SymExpr): Goal =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    // Open dependency: dropped 4 cases which require other function summary.
    List(
      AoCase(List(FTypeCheck(x, NumberT)), normal(x)),
      AoCase(
        List(FTypeCheck(x, SymbolT || BigIntT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      AoCase(List(FTypeCheck(x, UndefT)), normal(SELit(ENumber(Double.NaN)))),
      AoCase(
        List(FTypeCheck(x, NullT || FalseT)),
        normal(SELit(ENumber(0.0))),
      ),
      AoCase(List(FTypeCheck(x, TrueT)), normal(SELit(ENumber(1.0)))),
    )

  private val Contradiction = FEq(SELit(EBool(true)), SELit(EBool(false)))

  private def rewrite(f: Formula)(using CFG): List[Formula] = f match
    // Completion record wrappers
    case FTypeCheck(SEApp("NormalCompletion", List(x)), ty) if ty <= CompT =>
      if (ty <= AbruptT) List(Contradiction)
      else normalCompletionTypeConstraints(x, ty)
    case FTypeCheck(SEApp("Completion", List(x)), ty)
        if ty <= CompT && isCompletionExpr(x) =>
      List(FTypeCheck(x, ty))

    // 7.1 Type Conversion

    // https://tc39.es/ecma262/#sec-toboolean
    // ToBoolean is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-tonumber
    // ToNumber is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-tointegerorinfinity
    // NOTE: delegates to ToNumber
    case FTypeCheck(SEApp("ToIntegerOrInfinity", List(x)), ty) if ty <= CompT =>
      val toNumber = SEApp("ToNumber", List(x))
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(FTypeCheck(toNumber, ty))
        case _ => List(f)

    // https://tc39.es/ecma262/#sec-tobigint
    // ToBigInt is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-tostring
    // ToString is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-toobject
    // ToObject is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-tolength
    // NOTE: delegates to ToIntegerOrInfinity
    case FTypeCheck(SEApp("ToLength", List(x)), ty) if ty <= CompT =>
      val toIntegerOrInfinity = SEApp("ToIntegerOrInfinity", List(x))
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(FTypeCheck(toIntegerOrInfinity, ty))
        case _ => List(f)

    // https://tc39.es/ecma262/#sec-toindex
    // NOTE: delegates to ToIntegerOrInfinity
    case FTypeCheck(SEApp("ToIndex", List(x)), ty) if ty <= CompT =>
      val toIntegerOrInfinity = SEApp("ToIntegerOrInfinity", List(x))
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(FTypeCheck(toIntegerOrInfinity, ty))
        case _ => List(f)

    // 7.2 Testing and Comparison Operations

    // https://tc39.es/ecma262/#sec-requireobjectcoercible
    // RequireObjectCoercible is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-isarray
    // IsArray is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-iscallable
    // IsCallable is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-isconstructor
    // IsConstructor is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-isregexp
    // IsRegExp is modeled point-wise as implication facts.

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
      if (b) List(FTypeCheck(x, ObjectT))
      else List(FNot(FTypeCheck(x, ObjectT)), FNot(FTypeCheck(x, SymbolT)))

    // 10.1 Ordinary Object Internal Methods and Internal Slots

    // https://tc39.es/ecma262/#sec-requireinternalslot
    case FTypeCheck(
          SEApp("RequireInternalSlot", List(x, SELit(EStr(slot)))),
          ty,
        ) if ty <= CompT =>
      ty match
        case _ if ty <= NormalT =>
          List(FTypeCheck(x, ObjectT), FExists(x, SELit(EStr(slot))))
        case _ if ty <= AbruptT => List(FNot(FTypeCheck(x, ObjectT)))
        case _                  => List(f)

    // ThisXXXValue series (around 20.XX)

    // ThisXXXValue series (ThisSymbolValue, ThisNumberValue, ThisBigIntValue,
    // ThisStringValue, ThisBooleanValue) are modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-ordinarycreatefromconstructor
    // NOTE: delegates to Get(constructor, "prototype") via GetPrototypeFromConstructor
    case FTypeCheck(SEApp("OrdinaryCreateFromConstructor", List(ctor, _*)), ty)
        if ty <= CompT =>
      val getProto = SEApp("Get", List(ctor, SELit(EStr("prototype"))))
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(FTypeCheck(getProto, ty))
        case _ => List(f)

    // https://tc39.es/ecma262/#sec-installerrorcause
    // NOTE: delegates to HasProperty(options, "cause")
    case FTypeCheck(SEApp("InstallErrorCause", List(_, options)), ty)
        if ty <= CompT =>
      val hasCause = SEApp("HasProperty", List(options, SELit(EStr("cause"))))
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(FTypeCheck(hasCause, ty))
        case _ => List(f)

    // https://tc39.es/ecma262/#sec-validatenonrevokedproxy
    // NOTE: throws TypeError only if proxy is revoked (handler is null)
    case FTypeCheck(SEApp("ValidateNonRevokedProxy", List(o)), ty)
        if ty <= CompT =>
      val hasHandler = FExists(o, SELit(EStr("ProxyHandler")))
      ty match
        case _ if ty <= NormalT => List(hasHandler)
        case _ if ty <= AbruptT => List(FNot(hasHandler))
        case _                  => List(f)

    // https://tc39.es/ecma262/#sec-validatetypedarray
    // NOTE: delegates to RequireInternalSlot(typedArray, "TypedArrayName")
    case FTypeCheck(SEApp("ValidateTypedArray", List(o, _)), ty)
        if ty <= CompT =>
      ty match
        case _ if ty <= NormalT || ty <= AbruptT =>
          List(
            FTypeCheck(
              SEApp(
                "RequireInternalSlot",
                List(o, SELit(EStr("TypedArrayName"))),
              ),
              ty,
            ),
          )
        case _ => List(f)

    // 27.1 Iteration

    // https://tc39.es/ecma262/#sec-getiterator
    case FTypeCheck(SEApp("GetIterator", List(obj)), ty) if ty <= NormalT =>
      val methodResult = SEApp("Get", List(obj, SELit(EStr("iterator"))))
      val method = SEField(methodResult, "Value")
      val callResult = SEApp("Call", List(method, obj))
      List(
        FTypeCheck(methodResult, NormalT),
        FTypeCheck(callResult, NormalT),
        FTypeCheck(SEField(callResult, "Value"), ObjectT),
      )

    // https://tc39.es/ecma262/#sec-getiteratorfrommethod
    case FTypeCheck(SEApp("GetIteratorFromMethod", List(obj, method)), ty)
        if ty <= NormalT =>
      val callResult = SEApp("Call", List(method, obj))
      List(
        FTypeCheck(callResult, NormalT),
        FTypeCheck(SEField(callResult, "Value"), ObjectT),
      )

    // https://tc39.es/ecma262/#sec-iteratornext
    case FTypeCheck(SEApp("IteratorNext", iterRecord :: args), ty)
        if ty <= NormalT =>
      iteratorParts(iterRecord) match
        case Some(_) =>
          val result = iteratorNextResult(iterRecord, args)
          List(
            FTypeCheck(result, NormalT),
            FTypeCheck(SEField(result, "Value"), ObjectT),
          )
        case None => List(f)

    // https://tc39.es/ecma262/#sec-iteratorcomplete
    case FTypeCheck(SEApp("IteratorComplete", List(result)), ty)
        if ty <= NormalT =>
      val doneResult =
        SEApp("Get", List(iteratorResultValue(result), SELit(EStr("done"))))
      List(
        FTypeCheck(doneResult, NormalT),
        FTypeCheck(SEField(doneResult, "Value"), BoolT),
      )

    // https://tc39.es/ecma262/#sec-iteratorvalue
    case FTypeCheck(SEApp("IteratorValue", List(result)), ty)
        if ty <= NormalT =>
      val valueResult =
        SEApp("Get", List(iteratorResultValue(result), SELit(EStr("value"))))
      List(FTypeCheck(valueResult, NormalT))

    case _ => List(rewriteCompletionValues(f).getOrElse(f))

  // Converts .Type comparisons before rewrite while preserving completion
  // wrappers whose value semantics need explicit rewrite rules.

  private def stripCompletion(f: Formula): Formula = f match
    case FEq(TypeField(base), SELit(EEnum(e))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FTypeCheck(stripExpr(base), ty)
    case FEq(SELit(EEnum(e)), TypeField(base)) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FTypeCheck(stripExpr(base), ty)
    case FNot(inner)       => FNot(stripCompletion(inner))
    case FEq(l, r)         => FEq(stripExpr(l), stripExpr(r))
    case FLt(l, r)         => FLt(stripExpr(l), stripExpr(r))
    case FExists(b, k)     => FExists(stripExpr(b), k)
    case FTypeCheck(e, ty) => FTypeCheck(stripExpr(e), ty)

  private def stripExpr(t: SymExpr): SymExpr = t match
    case SETypeOf(inner)      => SETypeOf(stripExpr(inner))
    case SEProj(base, k)      => SEProj(stripExpr(base), stripExpr(k))
    case SEField(base, field) => SEField(stripExpr(base), field)
    case SEApp(op, args)      => SEApp(op, args.map(stripExpr))
    case SEList(elems)        => SEList(elems.map(stripExpr))
    case SERecord(tn, fields) =>
      SERecord(tn, fields.map((k, v) => k -> stripExpr(v)))
    case SEMap(entries) =>
      SEMap(entries.map((k, v) => stripExpr(k) -> stripExpr(v)))
    case _ => t

  // Normalizes value-level AO projections after rewrite.

  private def normalizeExpr(f: Formula): Formula = f match
    case FEq(TypeField(base), SELit(EEnum(e))) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FTypeCheck(reduceExpr(base), ty)
    case FEq(SELit(EEnum(e)), TypeField(base)) =>
      val ty = if (e == "normal") NormalT else AbruptT
      FTypeCheck(reduceExpr(base), ty)
    case FNot(inner)       => FNot(normalizeExpr(inner))
    case FEq(l, r)         => FEq(reduceExpr(l), reduceExpr(r))
    case FLt(l, r)         => FLt(reduceExpr(l), reduceExpr(r))
    case FExists(b, k)     => FExists(reduceExpr(b), k)
    case FTypeCheck(e, ty) => FTypeCheck(reduceExpr(e), ty)

  private def reduceExpr(t: SymExpr): SymExpr = t match
    case ValueField(SEApp("ToIntegerOrInfinity", List(x))) =>
      SEField(SEApp("ToNumber", List(reduceExpr(x))), "Value")
    case ValueField(SEApp("ToLength", List(x))) =>
      SEField(SEApp("ToNumber", List(reduceExpr(x))), "Value")
    case ValueField(SEApp("ToIndex", List(x))) =>
      SEField(SEApp("ToNumber", List(reduceExpr(x))), "Value")
    case ValueField(SEApp("ToPropertyKey", List(x))) =>
      reduceExpr(x)
    case SEApp("LengthOfArrayLike", List(x)) =>
      SEApp("Get", List(reduceExpr(x), SELit(EStr("length"))))
    case SEApp("GetMethod", List(v, SELit(EStr(p)))) =>
      SEApp("Get", List(reduceExpr(v), SELit(EStr(p))))
    case SEApp("GetMethod", List(v, SEProj(_, p))) =>
      SEApp("Get", List(reduceExpr(v), reduceExpr(p)))
    case SEApp("GetMethod", List(v, SEField(SEApp("SYMBOL", Nil), p))) =>
      SEApp("Get", List(reduceExpr(v), SELit(EStr(p))))
    case SEApp("__CLAMP__", List(x, _, _)) => reduceExpr(x)
    case SEApp("ToPropertyKey", List(x))   => reduceExpr(x)
    case SEApp("ToIntegerOrInfinity", List(x)) =>
      SEApp("ToNumber", List(reduceExpr(x)))
    case SEApp("ToLength", List(x)) =>
      SEApp("ToIntegerOrInfinity", List(reduceExpr(x)))
    case SEApp("ToIndex", List(x)) =>
      SEApp("ToIntegerOrInfinity", List(reduceExpr(x)))
    case SETypeOf(inner)      => SETypeOf(reduceExpr(inner))
    case ValueField(inner)    => SEField(reduceExpr(inner), "Value")
    case SEProj(base, k)      => SEProj(reduceExpr(base), reduceExpr(k))
    case SEField(base, field) => SEField(reduceExpr(base), field)
    case SEApp(op, args)      => SEApp(op, args.map(reduceExpr(_)))
    case SEList(elems)        => SEList(elems.map(reduceExpr(_)))
    case SERecord(tn, fields) =>
      SERecord(tn, fields.map((k, v) => k -> reduceExpr(v)))
    case SEMap(entries) =>
      SEMap(entries.map((k, v) => reduceExpr(k) -> reduceExpr(v)))
    case _ => t

  private def rewriteCompletionValues(
    f: Formula,
  )(using CFG): Option[Formula] = f match
    case FNot(inner) => rewriteCompletionValues(inner).map(FNot(_))
    case FEq(l, r) =>
      rewriteCompletionValueExpr(l)
        .map(FEq(_, r))
        .orElse(rewriteCompletionValueExpr(r).map(FEq(l, _)))
    case FLt(l, r) =>
      rewriteCompletionValueExpr(l)
        .map(FLt(_, r))
        .orElse(rewriteCompletionValueExpr(r).map(FLt(l, _)))
    case FExists(b, k) => rewriteCompletionValueExpr(b).map(FExists(_, k))
    case FTypeCheck(e, ty) =>
      rewriteCompletionValueExpr(e).map(FTypeCheck(_, ty))

  private def rewriteCompletionValueExpr(
    expr: SymExpr,
  )(using CFG): Option[SymExpr] =
    expr match
      case ValueField(SEApp("NormalCompletion", List(inner))) =>
        Some(reduceExpr(inner))
      case ValueField(SEApp("Completion", List(inner)))
          if isCompletionExpr(inner) =>
        Some(SEField(reduceExpr(inner), "Value"))
      case SETypeOf(inner) =>
        rewriteCompletionValueExpr(inner).map(SETypeOf(_))
      case SEProj(base, key) =>
        rewriteCompletionValueExpr(base)
          .map(SEProj(_, key))
          .orElse(rewriteCompletionValueExpr(key).map(SEProj(base, _)))
      case SEField(base, field) =>
        rewriteCompletionValueExpr(base).map(SEField(_, field))
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
    if (valueTy.isTop) Nil else List(FTypeCheck(value, valueTy))

  private def isCompletionExpr(
    expr: SymExpr,
  )(using cfg: CFG): Boolean = expr match
    case SEApp(name: String, _) =>
      cfg.fnameMap.get(name).forall(_.retTy.isCompletion)
    case _ => false

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
        SEField(iteratorNextResult(iterRecord, args), "Value")
      case app @ SEApp("Call", _) => SEField(app, "Value")
      case other                  => other
}
