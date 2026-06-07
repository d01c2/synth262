package esmeta.solver

import esmeta.cfg.CFG
import esmeta.ir.*
import esmeta.ty.*
import esmeta.util.*
import Formula.*, SymExpr.*

object RewriteRules {
  def rewriteFormula(f: Formula)(using CFG): List[Formula] =
    rewrite(stripCompletion(f)).map(normalizeExpr)

  def aoSummary(call: SymExpr): AOSummary =
    AOSummary(call, aoModel(call).flatMap(AOCase.fromFormula))

  def aoModel(call: SymExpr): List[Formula] = call match
    case SECall("ToNumber", List(x))  => toNumberModel(x, call)
    case SECall("ToBoolean", List(x)) => toBooleanModel(x, call)
    case SECall("ToObject", List(x))  => toObjectModel(x, call)
    case SECall("ToBigInt", List(x))  => toBigIntModel(x, call)
    case SECall("ToString", List(x))  => toStringModel(x, call)
    case SECall("RequireObjectCoercible", List(x)) =>
      requireObjectCoercibleModel(x, call)
    case SECall("ThisSymbolValue", List(x)) =>
      thisValueModel(x, call, SymbolT, "SymbolData")
    case SECall("ThisNumberValue", List(x)) =>
      thisValueModel(x, call, NumberT, "NumberData")
    case SECall("ThisBigIntValue", List(x)) =>
      thisValueModel(x, call, BigIntT, "BigIntData")
    case SECall("ThisStringValue", List(x)) =>
      thisValueModel(x, call, StrT, "StringData")
    case SECall("ThisBooleanValue", List(x)) =>
      thisValueModel(x, call, BoolT, "BooleanData")
    case SECall("IsArray", List(x))         => isArrayModel(x, call)
    case SECall("IsCallable", List(x))      => isCallableModel(x, call)
    case SECall("IsConstructor", List(x))   => isConstructorModel(x, call)
    case SECall("IsRegExp", List(x))        => isRegExpModel(x, call)
    case SECall("CanBeHeldWeakly", List(x)) => canBeHeldWeaklyModel(x, call)
    case SECall("RequireInternalSlot", List(x, slot)) =>
      requireInternalSlotModel(x, slot, call)
    case SECall("ValidateNonRevokedProxy", List(proxy)) =>
      validateNonRevokedProxyModel(proxy, call)
    case SECall("OrdinaryCreateFromConstructor", List(ctor, _*)) =>
      ordinaryCreateFromConstructorModel(ctor, call)
    case SECall("InstallErrorCause", List(_, options)) =>
      installErrorCauseModel(options, call)
    case SECall("ValidateTypedArray", List(o, _)) =>
      validateTypedArrayModel(o, call)
    case SECall("ToPrimitive", List(x, _*)) => toPrimitiveModel(x, call)
    case SECall("IsTypedArrayOutOfBounds", List(_)) =>
      isTypedArrayOutOfBoundsModel(call)
    case SECall("SameValue", List(x, y))     => sameValueModel(x, y, call)
    case SECall("SameValueZero", List(x, y)) => sameValueModel(x, y, call)
    case SECall("ToIntegerOrInfinity", List(x)) =>
      toIntegerOrInfinityModel(x, call)
    case SECall("ToLength", List(x))          => toLengthModel(x, call)
    case SECall("ToIndex", List(x))           => toIndexModel(x, call)
    case SECall("ToUint32", List(x))          => toUint32Model(x, call)
    case SECall("ToPropertyKey", List(x))     => toPropertyKeyModel(x, call)
    case SECall("LengthOfArrayLike", List(x)) => lengthOfArrayLikeModel(x, call)
    case SECall("CreateDataProperty", List(o, p, v)) =>
      createDataPropertyModel(o, p, v, call)
    case SECall("CreateDataPropertyOrThrow", List(o, p, v)) =>
      createDataPropertyOrThrowModel(o, p, v, call)
    case SECall("GetMethod", List(v, p)) => getMethodModel(v, p, call)
    case SECall("GetIterator", List(obj, kind)) =>
      getIteratorModel(obj, kind, call)
    case SECall("GetIteratorFromMethod", List(obj, method)) =>
      getIteratorFromMethodModel(obj, method, call)
    case SECall("GetIteratorDirect", List(obj)) =>
      getIteratorDirectModel(obj, call)
    case SECall("IteratorNext", iterRecord :: args) =>
      iteratorNextModel(iterRecord, args, call)
    case SECall("IteratorComplete", List(result)) =>
      iteratorCompleteModel(result, call)
    case SECall("IteratorValue", List(result)) =>
      iteratorValueModel(result, call)
    case SECall("IteratorStep", List(iterRecord)) =>
      iteratorStepModel(iterRecord, call)
    case SECall("IteratorStepValue", List(iterRecord)) =>
      iteratorStepValueModel(iterRecord, call)
    case SECall("IteratorClose", List(iterRecord, completion)) =>
      iteratorCloseModel(iterRecord, completion, call)
    case _ => Nil

  def isModeledCall(expr: SymExpr): Boolean = expr match
    case SECall("ToNumber", List(_))                 => true
    case SECall("ToBoolean", List(_))                => true
    case SECall("ToObject", List(_))                 => true
    case SECall("ToBigInt", List(_))                 => true
    case SECall("ToString", List(_))                 => true
    case SECall("RequireObjectCoercible", List(_))   => true
    case SECall("ThisSymbolValue", List(_))          => true
    case SECall("ThisNumberValue", List(_))          => true
    case SECall("ThisBigIntValue", List(_))          => true
    case SECall("ThisStringValue", List(_))          => true
    case SECall("ThisBooleanValue", List(_))         => true
    case SECall("IsArray", List(_))                  => true
    case SECall("IsCallable", List(_))               => true
    case SECall("IsConstructor", List(_))            => true
    case SECall("IsRegExp", List(_))                 => true
    case SECall("CanBeHeldWeakly", List(_))          => true
    case SECall("RequireInternalSlot", List(_, _))   => true
    case SECall("ValidateNonRevokedProxy", List(_))  => true
    case SECall("OrdinaryCreateFromConstructor", _)  => true
    case SECall("InstallErrorCause", List(_, _))     => true
    case SECall("ValidateTypedArray", List(_, _))    => true
    case SECall("ToPrimitive", _)                    => true
    case SECall("IsTypedArrayOutOfBounds", List(_))  => true
    case SECall("SameValue", List(_, _))             => true
    case SECall("SameValueZero", List(_, _))         => true
    case SECall("ToIntegerOrInfinity", List(_))      => true
    case SECall("ToLength", List(_))                 => true
    case SECall("ToIndex", List(_))                  => true
    case SECall("ToUint32", List(_))                 => true
    case SECall("ToPropertyKey", List(_))            => true
    case SECall("LengthOfArrayLike", List(_))        => true
    case SECall("CreateDataProperty", List(_, _, _)) => true
    case SECall("CreateDataPropertyOrThrow", List(_, _, _)) =>
      true
    case SECall("GetMethod", List(_, _))             => true
    case SECall("GetIterator", List(_, _))           => true
    case SECall("GetIteratorFromMethod", List(_, _)) => true
    case SECall("GetIteratorDirect", List(_))        => true
    case SECall("IteratorNext", _ :: _)              => true
    case SECall("IteratorComplete", List(_))         => true
    case SECall("IteratorValue", List(_))            => true
    case SECall("IteratorStep", List(_))             => true
    case SECall("IteratorStepValue", List(_))        => true
    case SECall("IteratorClose", List(_, _))         => true
    case _                                           => false

  private def toBooleanModel(x: SymExpr, ret: SymExpr): List[Formula] =
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    // return values cannot be inferred from detailed-types, so checked CFG
    List(
      FImply(List(FTypeCheck(x, UndefT)), List(FEq(ret, f))),
      FImply(List(FTypeCheck(x, NullT)), List(FEq(ret, f))),
      FImply(List(FTypeCheck(x, BoolT)), List(FEq(ret, x))),
      // detailed-types has no value-level BigInt; split via CFG branch `= argument 0n`
      FImply(
        List(FTypeCheck(x, BigIntT), FEq(x, SELit(EBigInt(BigInt(0))))),
        List(FEq(ret, f)),
      ),
      FImply(
        List(FTypeCheck(x, BigIntT), FNot(FEq(x, SELit(EBigInt(BigInt(0)))))),
        List(FEq(ret, t)),
      ),
      FImply(
        List(FTypeCheck(x, ValueTy(number = NumberIntTy(IntTy.Zero, true)))),
        List(FEq(ret, f)),
      ),
      FImply(
        List(
          FTypeCheck(
            x,
            ValueTy(number = NumberSignTy(Sign.Neg || Sign.Pos, false)),
          ),
        ),
        List(FEq(ret, t)),
      ),
      FImply(
        List(FTypeCheck(x, ValueTy(str = Fin(Set(""))))),
        List(FEq(ret, f)),
      ),
      FImply(
        List(FTypeCheck(x, StrT), FNot(FEq(x, SELit(EStr(""))))),
        List(FEq(ret, t)),
      ),
      FImply(List(FTypeCheck(x, SymbolT)), List(FEq(ret, t))),
      FImply(List(FTypeCheck(x, ObjectT)), List(FEq(ret, t))),
    )

  private def toObjectModel(x: SymExpr, ret: SymExpr): List[Formula] =
    val abrupt = List(FTypeCheck(ret, ThrowT))
    val normal = List(FTypeCheck(ret, NormalT))
    // Wrapper cases return new objects whose internal fields (e.g., Prototype,
    // BooleanData) are visible in CFG but not expressible as type constraints.
    // ret.Value only constrained for Object (identity).
    List(
      FImply(List(FTypeCheck(x, UndefT)), abrupt),
      FImply(List(FTypeCheck(x, NullT)), abrupt),
      FImply(List(FTypeCheck(x, BoolT)), normal),
      FImply(List(FTypeCheck(x, NumberT)), normal),
      FImply(List(FTypeCheck(x, StrT)), normal),
      FImply(List(FTypeCheck(x, SymbolT)), normal),
      FImply(List(FTypeCheck(x, BigIntT)), normal),
      FImply(
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
  ): List[Formula] =
    List(
      FImply(
        List(FTypeCheck(x, primTy)),
        List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), x)),
      ),
      FImply(
        List(FTypeCheck(x, ObjectT), FExists(x, SELit(EStr(slot)))),
        List(FTypeCheck(ret, NormalT)),
      ),
      FImply(
        List(FNot(FTypeCheck(x, primTy)), FNot(FExists(x, SELit(EStr(slot))))),
        List(FTypeCheck(ret, ThrowT)),
      ),
    )

  private def isCallableModel(x: SymExpr, ret: SymExpr): List[Formula] =
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    val hasCall = FExists(x, SELit(EStr("Call")))
    // 3 return nodes, all modeled. Returns Boolean directly (not a completion).
    // CFG checks `exists argument.Call`
    List(
      FImply(List(FNot(FTypeCheck(x, ObjectT))), List(FEq(ret, f))),
      FImply(List(FTypeCheck(x, ObjectT), hasCall), List(FEq(ret, t))),
      FImply(List(FTypeCheck(x, ObjectT), FNot(hasCall)), List(FEq(ret, f))),
    )

  private def isConstructorModel(x: SymExpr, ret: SymExpr): List[Formula] =
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    val hasConstruct = FExists(x, SELit(EStr("Construct")))
    // 3 return nodes, all modeled. Returns Boolean directly (not a completion).
    // CFG checks `exists argument.Construct`
    List(
      FImply(List(FNot(FTypeCheck(x, ObjectT))), List(FEq(ret, f))),
      FImply(List(FTypeCheck(x, ObjectT), hasConstruct), List(FEq(ret, t))),
      FImply(
        List(FTypeCheck(x, ObjectT), FNot(hasConstruct)),
        List(FEq(ret, f)),
      ),
    )

  private def canBeHeldWeaklyModel(x: SymExpr, ret: SymExpr): List[Formula] =
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    // 3 return nodes; dropped 1 inter-proc (5738 via KeyForSymbol).
    // Returns Boolean directly (not a completion).
    // Symbol case (registered vs unregistered) requires KeyForSymbol summary.
    // Second case: detailed-types only knows `#0: Symbol|...|Null` at node 5739;
    // the Symbol exclusion comes from CFG control flow (prior-branch narrowing).
    List(
      FImply(List(FTypeCheck(x, ObjectT)), List(FEq(ret, t))),
      FImply(
        List(FNot(FTypeCheck(x, ObjectT || SymbolT))),
        List(FEq(ret, f)),
      ),
    )

  private def isRegExpModel(x: SymExpr, ret: SymExpr): List[Formula] =
    def normal(v: SymExpr): List[Formula] =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    val symMatch = SEField(SEGlobal("SYMBOL"), SELit(EStr("match")))
    // 6 return nodes; dropped 1 inter-proc (1532 via ToBoolean);
    // 1 analysis dropped (1530).
    List(
      FImply(List(FNot(FTypeCheck(x, ObjectT))), normal(f)),
      FImply(
        List(
          FTypeCheck(x, ObjectT),
          FTypeCheck(SECall("Get", List(x, symMatch)), AbruptT),
        ),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(FTypeCheck(x, ObjectT), FExists(x, SELit(EStr("RegExpMatcher")))),
        normal(t),
      ),
      // node 1537: Object, no RegExpMatcher → false
      FImply(
        List(
          FTypeCheck(x, ObjectT),
          FNot(FExists(x, SELit(EStr("RegExpMatcher")))),
        ),
        normal(f),
      ),
    )

  private def isArrayModel(x: SymExpr, ret: SymExpr): List[Formula] =
    def normal(v: SymExpr): List[Formula] =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    // 6 return nodes; dropped 3 inter-proc (1493,1499,1500 via
    // ValidateNonRevokedProxy/recursive IsArray on ProxyExoticObject).
    // Third case: detailed-types only knows `#0: Record[Object]` at node 1501;
    // the "not Array, not Proxy" narrowing comes from CFG control flow, not
    // from occurrence typing — detailed-types cannot express prior-branch exclusion.
    List(
      FImply(List(FNot(FTypeCheck(x, ObjectT))), normal(f)),
      FImply(List(FTypeCheck(x, RecordT("Array"))), normal(t)),
      FImply( // This case cannot be inferred only from detailed-types
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
  ): List[Formula] =
    // 3 return nodes, all modeled.
    List(
      FImply(List(FTypeCheck(x, UndefT)), List(FTypeCheck(ret, ThrowT))),
      FImply(List(FTypeCheck(x, NullT)), List(FTypeCheck(ret, ThrowT))),
      FImply(
        List(FNot(FTypeCheck(x, UndefT || NullT))),
        List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), x)),
      ),
    )

  private def toStringModel(x: SymExpr, ret: SymExpr): List[Formula] =
    def normal(v: SymExpr): List[Formula] =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    // Dropped inter-proc: Number::toString, BigInt::toString (IR ops);
    // 1 analysis dropped (1390) due to infeasible Completion check.
    // Object case: ToPrimitive throw propagated; normal path depends on
    // recursive ToString(prim) which may still throw (e.g., Symbol).
    List(
      FImply(List(FTypeCheck(x, StrT)), normal(x)),
      FImply(List(FTypeCheck(x, SymbolT)), List(FTypeCheck(ret, ThrowT))),
      FImply(List(FTypeCheck(x, UndefT)), normal(SELit(EStr("undefined")))),
      FImply(List(FTypeCheck(x, NullT)), normal(SELit(EStr("null")))),
      FImply(List(FTypeCheck(x, TrueT)), normal(SELit(EStr("true")))),
      FImply(List(FTypeCheck(x, FalseT)), normal(SELit(EStr("false")))),
      FImply(
        List(
          FTypeCheck(x, ObjectT),
          FTypeCheck(SECall("ToPrimitive", List(x)), AbruptT),
        ),
        List(FTypeCheck(ret, ThrowT)),
      ),
    )

  private def toBigIntModel(x: SymExpr, ret: SymExpr): List[Formula] =
    def normal(v: SymExpr): List[Formula] =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    val abrupt = List(FTypeCheck(ret, ThrowT))
    // Dropped inter-proc: StringToBigInt (IR ops).
    // Object case: ToPrimitive throw propagated; normal path depends on
    // recursive ToBigInt(prim) which may still throw (e.g., Number).
    List(
      FImply(List(FTypeCheck(x, UndefT)), abrupt),
      FImply(List(FTypeCheck(x, NullT)), abrupt),
      FImply(List(FTypeCheck(x, NumberT)), abrupt),
      FImply(List(FTypeCheck(x, SymbolT)), abrupt),
      FImply(
        List(FTypeCheck(x, BoolT), FEq(x, SELit(EBool(true)))),
        normal(SELit(EBigInt(BigInt(1)))),
      ),
      FImply(
        List(FTypeCheck(x, BoolT), FEq(x, SELit(EBool(false)))),
        normal(SELit(EBigInt(BigInt(0)))),
      ),
      FImply(List(FTypeCheck(x, BigIntT)), normal(x)),
      FImply(
        List(
          FTypeCheck(x, ObjectT),
          FTypeCheck(SECall("ToPrimitive", List(x)), AbruptT),
        ),
        abrupt,
      ),
    )

  private def toNumberModel(x: SymExpr, ret: SymExpr): List[Formula] =
    def normal(v: SymExpr): List[Formula] =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    // Dropped inter-proc: StringToNumber (IR ops).
    // Object case: ToPrimitive throw propagated; normal path depends on
    // recursive ToNumber(prim) which may still throw (e.g., Symbol/BigInt).
    List(
      FImply(List(FTypeCheck(x, NumberT)), normal(x)),
      FImply(
        List(FTypeCheck(x, SymbolT || BigIntT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(List(FTypeCheck(x, UndefT)), normal(SELit(ENumber(Double.NaN)))),
      FImply(
        List(FTypeCheck(x, NullT || FalseT)),
        normal(SELit(ENumber(0.0))),
      ),
      FImply(List(FTypeCheck(x, TrueT)), normal(SELit(ENumber(1.0)))),
      FImply(
        List(
          FTypeCheck(x, ObjectT),
          FTypeCheck(SECall("ToPrimitive", List(x)), AbruptT),
        ),
        List(FTypeCheck(ret, ThrowT)),
      ),
    )

  // 3 return nodes, all modeled.
  private def requireInternalSlotModel(
    x: SymExpr,
    slot: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    List(
      FImply(List(FNot(FTypeCheck(x, ObjectT))), List(FTypeCheck(ret, ThrowT))),
      FImply(
        List(FTypeCheck(x, ObjectT), FNot(FExists(x, slot))),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(FTypeCheck(x, ObjectT), FExists(x, slot)),
        List(FTypeCheck(ret, NormalT)),
      ),
    )

  // 2 return nodes, all modeled.
  private def validateNonRevokedProxyModel(
    proxy: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val hasTarget = FExists(proxy, SELit(EStr("ProxyTarget")))
    List(
      FImply(List(FNot(hasTarget)), List(FTypeCheck(ret, ThrowT))),
      FImply(List(hasTarget), List(FTypeCheck(ret, NormalT))),
    )

  // 2 effective return nodes; dropped 1 structural (OrdinaryObjectCreate).
  // Get is an internal method wrapper understood by reify.
  private def ordinaryCreateFromConstructorModel(
    ctor: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val getProto = SECall("Get", List(ctor, SELit(EStr("prototype"))))
    List(
      FImply(
        List(FTypeCheck(getProto, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(FTypeCheck(getProto, NormalT)),
        List(FTypeCheck(ret, NormalT)),
      ),
    )

  // 5 return paths; modeled 5. HasProperty and Get are internal method
  // wrappers understood by reify. CreateNonEnumerableDataPropertyOrThrow
  // throw is unreachable for OrdinaryObject receivers.
  private def installErrorCauseModel(
    options: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val hasCause =
      SECall("HasProperty", List(options, SELit(EStr("cause"))))
    val getCause =
      SECall("Get", List(options, SELit(EStr("cause"))))
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    List(
      FImply(
        List(FNot(FTypeCheck(options, ObjectT))),
        List(FTypeCheck(ret, NormalT)),
      ),
      FImply(
        List(FTypeCheck(options, ObjectT), FTypeCheck(hasCause, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(
          FTypeCheck(options, ObjectT),
          FTypeCheck(hasCause, NormalT),
          FEq(SEField(hasCause, "Value"), f),
        ),
        List(FTypeCheck(ret, NormalT)),
      ),
      FImply(
        List(
          FTypeCheck(options, ObjectT),
          FTypeCheck(hasCause, NormalT),
          FEq(SEField(hasCause, "Value"), t),
          FTypeCheck(getCause, AbruptT),
        ),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(
          FTypeCheck(options, ObjectT),
          FTypeCheck(hasCause, NormalT),
          FEq(SEField(hasCause, "Value"), t),
          FTypeCheck(getCause, NormalT),
        ),
        List(FTypeCheck(ret, NormalT)),
      ),
    )

  // 3 return nodes; dropped 1 inter-proc (IsTypedArrayOutOfBounds throw).
  // RequireInternalSlot is modeled; nested modeled calls are discovered by
  // the solver's summary-closure pass.
  // 4 return nodes: 1 throw (RequireInternalSlot abrupt), 1 throw
  // (IsTypedArrayOutOfBounds true), 1 normal, 1 structural.
  private def validateTypedArrayModel(o: SymExpr, ret: SymExpr): List[Formula] =
    val reqSlot =
      SECall("RequireInternalSlot", List(o, SELit(EStr("TypedArrayName"))))
    List(
      FImply(
        List(FTypeCheck(reqSlot, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(FTypeCheck(reqSlot, NormalT)),
        List(FTypeCheck(ret, NormalT)),
      ),
      FImply(
        List(FTypeCheck(reqSlot, NormalT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
    )

  // 9 return nodes; modeled 2, dropped 7 inter-proc (Call to exotic
  // @@toPrimitive, OrdinaryToPrimitive loop+Get+IsCallable+Call chain).
  // Get is an internal method wrapper understood by reify.
  private def toPrimitiveModel(x: SymExpr, ret: SymExpr): List[Formula] =
    val symToPrimitive =
      SEField(SEGlobal("SYMBOL"), SELit(EStr("toPrimitive")))
    val getExotic = SECall("GetMethod", List(x, symToPrimitive))
    List(
      FImply(
        List(FNot(FTypeCheck(x, ObjectT))),
        List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), x)),
      ),
      FImply(
        List(FTypeCheck(x, ObjectT), FTypeCheck(getExotic, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
    )

  // 3 return nodes; conditions (buffer detachment, byte offsets) are not
  // expressible in this formula system. The operation returns Boolean
  // directly, but the exact value is intentionally left unconstrained.
  private def isTypedArrayOutOfBoundsModel(ret: SymExpr): List[Formula] =
    List(FImply(Nil, List(FTypeCheck(ret, BoolT))))

  // 6 return nodes: 1 throw, 4 exact normal, 1 structural.
  private def toIntegerOrInfinityModel(
    x: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val toNumber = SECall("ToNumber", List(x))
    val numVal = SEField(toNumber, "Value")
    def normal(v: SymExpr): List[Formula] =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), v))
    List(
      // node 1187: ToNumber abrupt
      FImply(
        List(FTypeCheck(toNumber, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      // node 1192: number is NaN → 0
      FImply(
        List(
          FTypeCheck(toNumber, NormalT),
          FEq(numVal, SELit(ENumber(Double.NaN))),
        ),
        normal(SELit(EMath(0))),
      ),
      // node 1192: number is +0 → 0
      FImply(
        List(FTypeCheck(toNumber, NormalT), FEq(numVal, SELit(ENumber(0.0)))),
        normal(SELit(EMath(0))),
      ),
      // node 1192: number is -0 → 0
      FImply(
        List(FTypeCheck(toNumber, NormalT), FEq(numVal, SELit(ENumber(-0.0)))),
        normal(SELit(EMath(0))),
      ),
      // node 1195: number is +INF → +INF
      FImply(
        List(
          FTypeCheck(toNumber, NormalT),
          FEq(numVal, SELit(ENumber(Double.PositiveInfinity))),
        ),
        normal(SELit(EInfinity(true))),
      ),
      // node 1198: number is -INF → -INF
      FImply(
        List(
          FTypeCheck(toNumber, NormalT),
          FEq(numVal, SELit(ENumber(Double.NegativeInfinity))),
        ),
        normal(SELit(EInfinity(false))),
      ),
      // node 1206: general finite → Normal (floor, value not expressible)
      FImply(
        List(FTypeCheck(toNumber, NormalT)),
        List(FTypeCheck(ret, NormalT)),
      ),
    )

  private val MaxSafeLength: SymExpr =
    SELit(EMath(BigDecimal("9007199254740991")))

  // 4 return nodes: 1 throw, len <= 0, 2^53-1 < len, and general normal.
  private def toLengthModel(x: SymExpr, ret: SymExpr): List[Formula] =
    val toIntOrInf = SECall("ToIntegerOrInfinity", List(x))
    val innerVal = SEField(toIntOrInf, "Value")
    List(
      // node 1449: ToIntegerOrInfinity abrupt
      FImply(
        List(FTypeCheck(toIntOrInf, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      // node 1454: len ≤ 0 → 0
      FImply(
        List(
          FTypeCheck(toIntOrInf, NormalT),
          FNot(FLt(SELit(EMath(0)), innerVal)),
        ),
        List(
          FTypeCheck(ret, NormalT),
          FEq(SEField(ret, "Value"), SELit(ENumber(0.0))),
        ),
      ),
      FImply(
        List(
          FTypeCheck(toIntOrInf, NormalT),
          FLt(MaxSafeLength, innerVal),
        ),
        List(
          FTypeCheck(ret, NormalT),
          FEq(SEField(ret, "Value"), MaxSafeLength),
        ),
      ),
      FImply(
        List(
          FTypeCheck(toIntOrInf, NormalT),
          FLt(SELit(EMath(0)), innerVal),
        ),
        List(FTypeCheck(ret, NormalT)),
      ),
    )

  // 4 return nodes: 1 throw (ToIntegerOrInfinity abrupt), 1 throw
  // (RangeError for out-of-range), 1 normal, 1 structural.
  // Normal case: ret.Value = toIntOrInf.Value (no value transformation,
  // only range check — value is identity when in range).
  private def toIndexModel(x: SymExpr, ret: SymExpr): List[Formula] =
    val toIntOrInf = SECall("ToIntegerOrInfinity", List(x))
    List(
      FImply(
        List(FTypeCheck(toIntOrInf, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(FTypeCheck(toIntOrInf, NormalT)),
        List(
          FTypeCheck(ret, NormalT),
          FEq(SEField(ret, "Value"), SEField(toIntOrInf, "Value")),
        ),
      ),
      FImply(
        List(FTypeCheck(toIntOrInf, NormalT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
    )

  // 7 modeled cases: 1 throw, 5 exact zero normal cases, 1 structural normal.
  private def toUint32Model(x: SymExpr, ret: SymExpr): List[Formula] =
    val toNumber = SECall("ToNumber", List(x))
    val numVal = SEField(toNumber, "Value")
    val zero = SELit(ENumber(0.0))
    val normalZero =
      List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), zero))
    List(
      FImply(
        List(FTypeCheck(toNumber, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(
          FTypeCheck(toNumber, NormalT),
          FEq(numVal, SELit(ENumber(Double.NaN))),
        ),
        normalZero,
      ),
      FImply(
        List(
          FTypeCheck(toNumber, NormalT),
          FEq(numVal, SELit(ENumber(Double.PositiveInfinity))),
        ),
        normalZero,
      ),
      FImply(
        List(
          FTypeCheck(toNumber, NormalT),
          FEq(numVal, SELit(ENumber(Double.NegativeInfinity))),
        ),
        normalZero,
      ),
      FImply(
        List(FTypeCheck(toNumber, NormalT), FEq(numVal, SELit(ENumber(0.0)))),
        normalZero,
      ),
      FImply(
        List(FTypeCheck(toNumber, NormalT), FEq(numVal, SELit(ENumber(-0.0)))),
        normalZero,
      ),
      FImply(
        List(FTypeCheck(toNumber, NormalT)),
        List(FTypeCheck(ret, NormalT)),
      ),
    )

  // 4 return nodes: 1 throw (ToPrimitive abrupt), 1 normal (Symbol
  // identity), 1 normal (ToString), 1 structural.
  private def toPropertyKeyModel(x: SymExpr, ret: SymExpr): List[Formula] =
    val toPrim = SECall("ToPrimitive", List(x, SELit(EEnum("string"))))
    val primVal = SEField(toPrim, "Value")
    List(
      // node 1436: ToPrimitive abrupt
      FImply(List(FTypeCheck(toPrim, AbruptT)), List(FTypeCheck(ret, ThrowT))),
      // node 1443: key is Symbol → ret.Value = key
      FImply(
        List(FTypeCheck(toPrim, NormalT), FTypeCheck(primVal, SymbolT)),
        List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), primVal)),
      ),
      // node 1445: key is not Symbol → ToString(key)
      FImply(
        List(FTypeCheck(toPrim, NormalT), FNot(FTypeCheck(primVal, SymbolT))),
        List(
          FTypeCheck(ret, NormalT),
          FEq(
            SEField(ret, "Value"),
            SEField(SECall("ToString", List(primVal)), "Value"),
          ),
        ),
      ),
    )

  // 4 return nodes: 1 throw (Get abrupt), 1 throw (ToLength abrupt),
  // 1 normal, 1 structural.
  private def lengthOfArrayLikeModel(
    obj: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val getLength = SECall("Get", List(obj, SELit(EStr("length"))))
    val toLength = SECall("ToLength", List(SEField(getLength, "Value")))
    List(
      // node 2020: Get abrupt
      FImply(
        List(FTypeCheck(getLength, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      // node 2025: ToLength abrupt
      FImply(
        List(FTypeCheck(getLength, NormalT), FTypeCheck(toLength, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      // node 2031: Normal[Int[0+]]
      FImply(
        List(FTypeCheck(getLength, NormalT), FTypeCheck(toLength, NormalT)),
        List(
          FTypeCheck(ret, NormalT),
          FEq(SEField(ret, "Value"), SEField(toLength, "Value")),
        ),
      ),
    )

  private def createDataPropertyModel(
    o: SymExpr,
    p: SymExpr,
    v: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val desc = SERecord(
      "PropertyDescriptor",
      Map(
        "Value" -> v,
        "Writable" -> SELit(EBool(true)),
        "Enumerable" -> SELit(EBool(true)),
        "Configurable" -> SELit(EBool(true)),
      ),
    )
    val define = SECall("DefineOwnProperty", List(o, o, p, desc))
    List(
      FImply(
        List(FTypeCheck(define, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(FTypeCheck(define, NormalT)),
        List(
          FTypeCheck(ret, NormalT),
          FEq(SEField(ret, "Value"), SEField(define, "Value")),
        ),
      ),
    )

  private def createDataPropertyOrThrowModel(
    o: SymExpr,
    p: SymExpr,
    v: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val create = SECall("CreateDataProperty", List(o, p, v))
    val success = SEField(create, "Value")
    List(
      FImply(
        List(FTypeCheck(create, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(FTypeCheck(create, NormalT), FEq(success, SELit(EBool(false)))),
        List(FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(FTypeCheck(create, NormalT), FEq(success, SELit(EBool(true)))),
        List(FTypeCheck(ret, NormalT)),
      ),
    )

  // 5 return nodes: 1 throw (GetV abrupt), 1 normal (undefined/null →
  // undefined), 1 throw (not callable), 1 normal (callable func),
  // 1 structural.
  private def getMethodModel(
    v: SymExpr,
    p: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val getResult = SECall("Get", List(v, p))
    val getVal = SEField(getResult, "Value")
    List(
      // node 1870: GetV abrupt
      FImply(
        List(FTypeCheck(getResult, AbruptT)),
        List(FTypeCheck(ret, ThrowT)),
      ),
      // node 1875: func is undefined or null → Normal[Undefined]
      FImply(
        List(
          FTypeCheck(getResult, NormalT),
          FTypeCheck(getVal, UndefT || NullT),
        ),
        List(
          FTypeCheck(ret, NormalT),
          FEq(SEField(ret, "Value"), SELit(EUndef())),
        ),
      ),
      // node 1880: func not callable → Throw (TypeError)
      FImply(
        List(
          FTypeCheck(getResult, NormalT),
          FNot(FTypeCheck(getVal, UndefT || NullT)),
          FEq(SECall("IsCallable", List(getVal)), SELit(EBool(false))),
        ),
        List(FTypeCheck(ret, ThrowT)),
      ),
      // node 1884: func is callable → Normal, Value = func
      FImply(
        List(
          FTypeCheck(getResult, NormalT),
          FEq(SECall("IsCallable", List(getVal)), SELit(EBool(true))),
        ),
        List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), getVal)),
      ),
    )

  private def normalReturn(ret: SymExpr): List[Formula] =
    List(FTypeCheck(ret, NormalT))

  private def normalReturn(ret: SymExpr, value: SymExpr): List[Formula] =
    List(FTypeCheck(ret, NormalT), FEq(SEField(ret, "Value"), value))

  private def throwReturn(ret: SymExpr): List[Formula] =
    List(FTypeCheck(ret, ThrowT))

  private def prop(name: String): SymExpr = SELit(EStr(name))

  private def enumLit(name: String): SymExpr = SELit(EEnum(name))

  private def bool(value: Boolean): SymExpr = SELit(EBool(value))

  private def symbol(name: String): SymExpr =
    SEField(SEGlobal("SYMBOL"), prop(name))

  private def getIteratorModel(
    obj: SymExpr,
    kind: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val asyncKind = enumLit("async")
    val syncKind = enumLit("sync")
    val getAsyncMethod = SECall("GetMethod", List(obj, symbol("asyncIterator")))
    val asyncMethod = SEField(getAsyncMethod, "Value")
    val getSyncMethod = SECall("GetMethod", List(obj, symbol("iterator")))
    val syncMethod = SEField(getSyncMethod, "Value")
    val fromAsync = SECall("GetIteratorFromMethod", List(obj, asyncMethod))
    val fromSync = SECall("GetIteratorFromMethod", List(obj, syncMethod))
    val createAsync =
      SECall("CreateAsyncFromSyncIterator", List(SEField(fromSync, "Value")))
    List(
      FImply(
        List(FEq(kind, asyncKind), FTypeCheck(getAsyncMethod, AbruptT)),
        throwReturn(ret),
      ),
      FImply(
        List(
          FEq(kind, asyncKind),
          FTypeCheck(getAsyncMethod, NormalT),
          FEq(asyncMethod, SELit(EUndef())),
          FTypeCheck(getSyncMethod, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FEq(kind, asyncKind),
          FTypeCheck(getAsyncMethod, NormalT),
          FEq(asyncMethod, SELit(EUndef())),
          FTypeCheck(getSyncMethod, NormalT),
          FEq(syncMethod, SELit(EUndef())),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FEq(kind, asyncKind),
          FTypeCheck(getAsyncMethod, NormalT),
          FEq(asyncMethod, SELit(EUndef())),
          FTypeCheck(getSyncMethod, NormalT),
          FNot(FEq(syncMethod, SELit(EUndef()))),
          FTypeCheck(fromSync, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FEq(kind, asyncKind),
          FTypeCheck(getAsyncMethod, NormalT),
          FEq(asyncMethod, SELit(EUndef())),
          FTypeCheck(getSyncMethod, NormalT),
          FNot(FEq(syncMethod, SELit(EUndef()))),
          FTypeCheck(fromSync, NormalT),
          FTypeCheck(createAsync, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FEq(kind, asyncKind),
          FTypeCheck(getAsyncMethod, NormalT),
          FEq(asyncMethod, SELit(EUndef())),
          FTypeCheck(getSyncMethod, NormalT),
          FNot(FEq(syncMethod, SELit(EUndef()))),
          FTypeCheck(fromSync, NormalT),
          FTypeCheck(createAsync, RecordT("IteratorRecord")),
        ),
        normalReturn(ret, createAsync),
      ),
      FImply(
        List(FEq(kind, syncKind), FTypeCheck(getSyncMethod, AbruptT)),
        throwReturn(ret),
      ),
      FImply(
        List(
          FEq(kind, syncKind),
          FTypeCheck(getSyncMethod, NormalT),
          FEq(syncMethod, SELit(EUndef())),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FEq(kind, syncKind),
          FTypeCheck(getSyncMethod, NormalT),
          FNot(FEq(syncMethod, SELit(EUndef()))),
          FTypeCheck(fromSync, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FEq(kind, syncKind),
          FTypeCheck(getSyncMethod, NormalT),
          FNot(FEq(syncMethod, SELit(EUndef()))),
          FTypeCheck(fromSync, NormalT),
        ),
        normalReturn(ret, SEField(fromSync, "Value")),
      ),
      FImply(
        List(
          FEq(kind, asyncKind),
          FTypeCheck(getAsyncMethod, NormalT),
          FNot(FEq(asyncMethod, SELit(EUndef()))),
          FTypeCheck(fromAsync, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FEq(kind, asyncKind),
          FTypeCheck(getAsyncMethod, NormalT),
          FNot(FEq(asyncMethod, SELit(EUndef()))),
          FTypeCheck(fromAsync, NormalT),
        ),
        normalReturn(ret, SEField(fromAsync, "Value")),
      ),
    )

  private def getIteratorFromMethodModel(
    obj: SymExpr,
    method: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val callResult = SECall("Call", List(method, obj))
    val iterator = SEField(callResult, "Value")
    val direct = SECall("GetIteratorDirect", List(iterator))
    List(
      FImply(
        List(FTypeCheck(callResult, AbruptT)),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(callResult, NormalT),
          FNot(FTypeCheck(iterator, ObjectT)),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(callResult, NormalT),
          FTypeCheck(iterator, ObjectT),
          FTypeCheck(direct, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(callResult, NormalT),
          FTypeCheck(iterator, ObjectT),
          FTypeCheck(direct, NormalT),
        ),
        normalReturn(ret, SEField(direct, "Value")),
      ),
    )

  private def getIteratorDirectModel(
    obj: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val getNext = SECall("Get", List(obj, prop("next")))
    val nextMethod = SEField(getNext, "Value")
    val record = SERecord(
      "IteratorRecord",
      Map(
        "Iterator" -> obj,
        "NextMethod" -> nextMethod,
        "Done" -> bool(false),
      ),
    )
    val retValue = SEField(ret, "Value")
    List(
      FImply(
        List(FTypeCheck(obj, ObjectT), FTypeCheck(getNext, AbruptT)),
        throwReturn(ret),
      ),
      FImply(
        List(FTypeCheck(obj, ObjectT), FTypeCheck(getNext, NormalT)),
        normalReturn(ret, record) ++ List(
          FTypeCheck(retValue, RecordT("IteratorRecord")),
          FEq(SEField(retValue, "Iterator"), obj),
          FEq(SEField(retValue, "NextMethod"), nextMethod),
          FEq(SEField(retValue, "Done"), bool(false)),
        ),
      ),
    )

  private def iteratorNextModel(
    iterRecord: SymExpr,
    args: List[SymExpr],
    ret: SymExpr,
  ): List[Formula] =
    val result = iteratorNextResult(iterRecord, args)
    val resultValue = SEField(result, "Value")
    List(
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(result, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(result, NormalT),
          FNot(FTypeCheck(resultValue, ObjectT)),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(result, NormalT),
          FTypeCheck(resultValue, ObjectT),
        ),
        normalReturn(ret, resultValue),
      ),
    )

  private def iteratorCompleteModel(
    result: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val iteratorResult = iteratorResultValue(result)
    val doneResult = SECall("Get", List(iteratorResult, prop("done")))
    val doneValue = SEField(doneResult, "Value")
    val toBoolean = SECall("ToBoolean", List(doneValue))
    List(
      FImply(
        List(
          FTypeCheck(iteratorResult, ObjectT),
          FTypeCheck(doneResult, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(iteratorResult, ObjectT),
          FTypeCheck(doneResult, NormalT),
        ),
        normalReturn(ret, toBoolean),
      ),
    )

  private def iteratorValueModel(
    result: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val iteratorResult = iteratorResultValue(result)
    val valueResult = SECall("Get", List(iteratorResult, prop("value")))
    List(
      FImply(
        List(
          FTypeCheck(iteratorResult, ObjectT),
          FTypeCheck(valueResult, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(iteratorResult, ObjectT),
          FTypeCheck(valueResult, NormalT),
        ),
        normalReturn(ret, SEField(valueResult, "Value")),
      ),
    )

  private def iteratorStepModel(
    iterRecord: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val next = SECall("IteratorNext", List(iterRecord))
    val result = SEField(next, "Value")
    val done = SECall("IteratorComplete", List(result))
    val doneValue = SEField(done, "Value")
    List(
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(next, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(next, NormalT),
          FTypeCheck(done, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(next, NormalT),
          FTypeCheck(done, NormalT),
          FEq(doneValue, bool(true)),
        ),
        normalReturn(ret, enumLit("done")),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(next, NormalT),
          FTypeCheck(done, NormalT),
          FEq(doneValue, bool(false)),
        ),
        normalReturn(ret, result),
      ),
    )

  private def iteratorStepValueModel(
    iterRecord: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val step = SECall("IteratorStep", List(iterRecord))
    val result = SEField(step, "Value")
    val value = SECall("IteratorValue", List(result))
    List(
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(step, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(step, NormalT),
          FEq(result, enumLit("done")),
        ),
        normalReturn(ret, enumLit("done")),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(step, NormalT),
          FNot(FEq(result, enumLit("done"))),
          FTypeCheck(value, AbruptT),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(step, NormalT),
          FNot(FEq(result, enumLit("done"))),
          FTypeCheck(value, NormalT),
        ),
        normalReturn(ret, SEField(value, "Value")),
      ),
    )

  private def iteratorCloseModel(
    iterRecord: SymExpr,
    completion: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val iterator = iteratorRecordParts(iterRecord)._1
    val getReturn = SECall("GetMethod", List(iterator, prop("return")))
    val returnMethod = SEField(getReturn, "Value")
    val callReturn = SECall("Call", List(returnMethod, iterator))
    val callReturnValue = SEField(callReturn, "Value")
    List(
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(getReturn, NormalT),
          FEq(returnMethod, SELit(EUndef())),
          FTypeCheck(completion, AbruptT),
        ),
        List(FEq(ret, completion)),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(getReturn, NormalT),
          FEq(returnMethod, SELit(EUndef())),
          FTypeCheck(completion, NormalT),
        ),
        List(FEq(ret, completion)),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(completion, ThrowT),
        ),
        List(FEq(ret, completion)),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(completion, NormalT),
          FTypeCheck(getReturn, AbruptT),
        ),
        List(FEq(ret, getReturn), FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(completion, NormalT),
          FTypeCheck(getReturn, NormalT),
          FNot(FEq(returnMethod, SELit(EUndef()))),
          FTypeCheck(callReturn, AbruptT),
        ),
        List(FEq(ret, callReturn), FTypeCheck(ret, ThrowT)),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(completion, NormalT),
          FTypeCheck(getReturn, NormalT),
          FNot(FEq(returnMethod, SELit(EUndef()))),
          FTypeCheck(callReturn, NormalT),
          FNot(FTypeCheck(callReturnValue, ObjectT)),
        ),
        throwReturn(ret),
      ),
      FImply(
        List(
          FTypeCheck(iteratorRecordExpr(iterRecord), RecordT("IteratorRecord")),
          FTypeCheck(completion, NormalT),
          FTypeCheck(getReturn, NormalT),
          FNot(FEq(returnMethod, SELit(EUndef()))),
          FTypeCheck(callReturn, NormalT),
          FTypeCheck(callReturnValue, ObjectT),
        ),
        List(FEq(ret, completion)),
      ),
    )

  // 11 return nodes across SameValue + SameValueNonNumber;
  // all modeled cases reduce to equality check. 2 inter-proc dropped
  // (Number::sameValue, BigInt::equal — IR ops).
  // SameValueZero shares the same model (solver FEq does not
  // distinguish +0/-0 semantics).
  private def sameValueModel(
    x: SymExpr,
    y: SymExpr,
    ret: SymExpr,
  ): List[Formula] =
    val t = SELit(EBool(true))
    val f = SELit(EBool(false))
    List(
      FImply(List(FEq(x, y)), List(FEq(ret, t))),
      FImply(List(FNot(FEq(x, y))), List(FEq(ret, f))),
    )

  private val Contradiction = FEq(SELit(EBool(true)), SELit(EBool(false)))

  private def rewrite(f: Formula)(using CFG): List[Formula] = f match
    // Completion record wrappers
    case FTypeCheck(SECall("NormalCompletion", List(x)), ty) if ty <= CompT =>
      if (ty <= AbruptT) List(Contradiction)
      else normalCompletionTypeConstraints(x, ty)
    case FTypeCheck(SECall("Completion", List(x)), ty)
        if ty <= CompT && isCompletionExpr(x) =>
      List(FTypeCheck(x, ty))

    // 7.1 Type Conversion

    // https://tc39.es/ecma262/#sec-toboolean
    // ToBoolean is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-tonumber
    // ToNumber is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-tointegerorinfinity
    // ToIntegerOrInfinity is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-tobigint
    // ToBigInt is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-tostring
    // ToString is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-toobject
    // ToObject is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-tolength
    // ToLength is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-toindex
    // ToIndex is modeled point-wise as implication facts.

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
    // SameValue is modeled point-wise as implication facts.

    // https://tc39.es/ecma262/#sec-samevaluezero
    // SameValueZero is modeled point-wise as implication facts.

    case _ => List(rewriteCompletionValues(f).getOrElse(f))

  // Converts .Type comparisons before rewrite while preserving completion
  // wrappers whose value semantics need explicit rewrite rules.

  private def stripCompletion(f: Formula): Formula = f match
    case FImply(premise, conclusion) =>
      FImply(premise.map(stripCompletion), conclusion.map(stripCompletion))
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
    case SETypeOf(inner)    => SETypeOf(stripExpr(inner))
    case SEField(base, key) => SEField(stripExpr(base), stripExpr(key))
    case SEApp(op, args)    => SEApp(op, args.map(stripExpr))
    case SEList(elems)      => SEList(elems.map(stripExpr))
    case SERecord(tn, fields) =>
      SERecord(tn, fields.map((k, v) => k -> stripExpr(v)))
    case SEMap(entries) =>
      SEMap(entries.map((k, v) => stripExpr(k) -> stripExpr(v)))
    case _ => t

  // Normalizes value-level AO projections after rewrite.

  private def normalizeExpr(f: Formula): Formula = f match
    case FImply(premise, conclusion) =>
      FImply(premise.map(normalizeExpr), conclusion.map(normalizeExpr))
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
    case SEResidual("__CLAMP__", List(x, _, _)) => reduceExpr(x)
    case SETypeOf(inner)                        => SETypeOf(reduceExpr(inner))
    case ValueField(inner)  => SEField(reduceExpr(inner), "Value")
    case SEField(base, key) => SEField(reduceExpr(base), reduceExpr(key))
    case SEApp(op, args)    => SEApp(op, args.map(reduceExpr(_)))
    case SEList(elems)      => SEList(elems.map(reduceExpr(_)))
    case SERecord(tn, fields) =>
      SERecord(tn, fields.map((k, v) => k -> reduceExpr(v)))
    case SEMap(entries) =>
      SEMap(entries.map((k, v) => reduceExpr(k) -> reduceExpr(v)))
    case _ => t

  private def rewriteCompletionValues(
    f: Formula,
  )(using CFG): Option[Formula] = f match
    case FImply(premise, conclusion) =>
      val nextPremise =
        premise.map(f => rewriteCompletionValues(f).getOrElse(f))
      val nextConclusion =
        conclusion.map(f => rewriteCompletionValues(f).getOrElse(f))
      Option.when(nextPremise != premise || nextConclusion != conclusion)(
        FImply(nextPremise, nextConclusion),
      )
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
      case ValueField(SECall("NormalCompletion", List(inner))) =>
        Some(reduceExpr(inner))
      case ValueField(SECall("Completion", List(inner)))
          if isCompletionExpr(inner) =>
        Some(SEField(reduceExpr(inner), "Value"))
      case SETypeOf(inner) =>
        rewriteCompletionValueExpr(inner).map(SETypeOf(_))
      case SEField(base, key) =>
        rewriteCompletionValueExpr(base)
          .map(SEField(_, key))
          .orElse(rewriteCompletionValueExpr(key).map(SEField(base, _)))
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
    case SECall(name, _) =>
      cfg.fnameMap.get(name).forall(_.retTy.isCompletion)
    case _ => false

  private def iteratorRecordExpr(iterRecord: SymExpr): SymExpr =
    reduceExpr(iterRecord)

  private def iteratorRecordParts(
    iterRecord: SymExpr,
  ): (SymExpr, SymExpr, SymExpr) =
    iteratorParts(iterRecord).getOrElse {
      val record = iteratorRecordExpr(iterRecord)
      (
        SEField(record, "Iterator"),
        SEField(record, "NextMethod"),
        SEField(record, "Done"),
      )
    }

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
      case ValueField(SECall("GetIteratorDirect", List(obj))) =>
        Some(iteratorPartsFromObject(obj))
      case ValueField(SECall("GetIteratorFromMethod", List(obj, method))) =>
        val iterator = SEField(SECall("Call", List(method, obj)), "Value")
        Some(iteratorPartsFromObject(iterator))
      case ValueField(SECall("GetIterator", List(obj, SELit(EEnum("sync"))))) =>
        val method =
          SEField(SECall("GetMethod", List(obj, symbol("iterator"))), "Value")
        val iterator = SEField(SECall("Call", List(method, obj)), "Value")
        Some(iteratorPartsFromObject(iterator))
      case _ => None

  private def iteratorPartsFromObject(
    iterator: SymExpr,
  ): (SymExpr, SymExpr, SymExpr) =
    val nextMethod =
      SEField(SECall("Get", List(iterator, prop("next"))), "Value")
    (reduceExpr(iterator), nextMethod, bool(false))

  private def iteratorNextResult(
    iterRecord: SymExpr,
    args: List[SymExpr],
  ): SymExpr =
    val (iterator, nextMethod, _) = iteratorRecordParts(iterRecord)
    val callArgs = List(nextMethod, iterator) ++ args.map(reduceExpr)
    SECall("Call", callArgs)

  private def iteratorResultValue(result: SymExpr): SymExpr =
    reduceExpr(result) match
      case SECall("IteratorNext", iterRecord :: args) =>
        SEField(iteratorNextResult(iterRecord, args), "Value")
      case app @ SECall("Call", _) => SEField(app, "Value")
      case other                   => other
}
