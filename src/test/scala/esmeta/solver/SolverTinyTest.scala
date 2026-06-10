package esmeta.solver

import esmeta.cfg.{Block, Branch, BranchKind, CFG, Func as CFGFunc}
import esmeta.es.util.Coverage.Cond
import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*

/** basic solver test */
class SolverTinyTest extends SolverTest {
  val name: String = "solverTinyTest"
  private def expand(goal: List[Formula]): List[Formula] = solver.expand(goal)

  def init: Unit = {
    import SolverTest.*

    checkUnsat("contradiction: x == 0 and x == 1")(
      List(isValue(xSym, EMath(0)), isValue(xSym, EMath(1))),
    )

    checkUnsat("contradiction: x == x and NOT(x == x)")(
      List(FEq(xSym, xSym), FNot(FEq(xSym, xSym))),
    )

    checkUnsat("contradiction: x == undefined and x is Symbol")(
      List(isValue(xSym, EUndef()), isType(xSym, SymbolT)),
    )

    checkUnsat("contradiction: x == undefined and x is not Undefined")(
      List(isValue(xSym, EUndef()), isNotType(xSym, UndefT)),
    )

    check("literal ordering treats infinity as unbounded") {
      val huge = SELit(EMath(BigDecimal("1e400")))
      val posInf = SELit(EInfinity(true))
      val negInf = SELit(EInfinity(false))

      assert(solver.saturate(List(FLt(huge, posInf))) == Some(Nil))
      assert(solver.saturate(List(FLt(posInf, huge))).isEmpty)
      assert(solver.saturate(List(FLt(negInf, huge))) == Some(Nil))
      assert(solver.saturate(List(FNot(FLt(huge, posInf)))).isEmpty)
    }

    check("GetIterator normal keeps Call completion separate from its value") {
      val call = SECall("Call", List(ySym, xSym))
      val value = SEField(call, "Value")
      val model =
        RewriteRules.aoModel(SECall("GetIteratorFromMethod", List(xSym, ySym)))

      assert(
        model.exists {
          case FImply(when, _) =>
            when.contains(isType(call, NormalT)) &&
            when.contains(isType(value, ObjectT))
          case _ => false
        },
      )
      assert(
        !model.exists {
          case FImply(when, conclusion) =>
            (when ++ conclusion).contains(isType(call, ObjectT))
          case _ => false
        },
      )
    }

    check("IteratorNext normal keeps Call completion separate from its value") {
      val iterRecord = SERecord(
        "IteratorRecord",
        Map(
          "Iterator" -> xSym,
          "NextMethod" -> ySym,
          "Done" -> SELit(EBool(false)),
        ),
      )
      val call = SECall("Call", List(ySym, xSym))
      val value = SEField(call, "Value")
      val model = RewriteRules.aoModel(SECall("IteratorNext", List(iterRecord)))

      assert(
        model.exists {
          case FImply(when, _) =>
            when.contains(isType(call, NormalT)) &&
            when.contains(isType(value, ObjectT))
          case _ => false
        },
      )
      assert(
        !model.exists {
          case FImply(when, conclusion) =>
            (when ++ conclusion).contains(isType(call, ObjectT))
          case _ => false
        },
      )
    }

    check("ToNumber value projection is not rewritten into its input") {
      val value =
        SEField(SECall("ToNumber", List(xSym)), "Value")
      val expanded = expand(List(isValue(value, EMath(1))))

      assert(expanded.contains(isValue(value, EMath(1))))
      assert(!expanded.contains(isValue(xSym, EMath(1))))
      assert(!expanded.contains(isType(xSym, NumberT)))
    }

    check("ToNumber model has six point-wise cases") {
      val toNumber = SECall("ToNumber", List(xSym))
      val value = SEField(toNumber, "Value")
      val cases = RewriteRules.aoModel(toNumber)

      assert(cases.size == 6)
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when == List(isType(xSym, NumberT)) &&
            conclusion == List(isType(toNumber, NormalT), FEq(value, xSym))
          case _ => false
        },
      )
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when == List(isType(xSym, UndefT)) &&
            conclusion == List(
              isType(toNumber, NormalT),
              FEq(value, SELit(ENumber(Double.NaN))),
            )
          case _ => false
        },
      )
    }

    check("aoModel exposes raw implication formulas") {
      val toNumber = SECall("ToNumber", List(xSym))
      val value = SEField(toNumber, "Value")
      val numberImplication = FImply(
        List(isType(xSym, NumberT)),
        List(isType(toNumber, NormalT), FEq(value, xSym)),
      )

      assert(RewriteRules.aoModel(toNumber).contains(numberImplication))
    }

    check("FImply discharges only when its premise is known") {
      val premise = isType(xSym, NumberT)
      val conclusion = isValue(ySym, EMath(1))
      val implication = FImply(List(premise), List(conclusion))
      val inactive = solver
        .saturate(List(implication))
        .getOrElse(fail("expected inactive implication to be satisfiable"))
      val active = solver
        .saturate(List(premise, implication))
        .getOrElse(fail("expected active implication to be satisfiable"))

      assert(!inactive.contains(conclusion))
      assert(active.contains(conclusion))
    }

    check("ToNumber value requirement is solved by summary cases") {
      val toNumber = SECall("ToNumber", List(xSym))
      val solved = solver
        .solve(List(isValue(SEField(toNumber, "Value"), ENumber(1.0))))
        .getOrElse(fail("expected satisfiable ToNumber goal"))

      assert(solved.contains(isType(xSym, NumberT)))
      assert(solved.contains(isValue(xSym, ENumber(1.0))))
      assert(!solved.exists(_.toString.contains("ToNumber")))
    }

    check("ToNumber model does not activate from input-only constraints") {
      val solved = solver
        .solve(List(isType(xSym, NumberT)))
        .getOrElse(fail("expected satisfiable input-only goal"))

      assert(solved == List(isType(xSym, NumberT)))
    }

    check("ToNumber undefined can satisfy a NaN result") {
      val toNumber = SECall("ToNumber", List(xSym))
      val solved = solver
        .solve(
          List(
            isType(xSym, UndefT),
            isValue(SEField(toNumber, "Value"), ENumber(Double.NaN)),
          ),
        )
        .getOrElse(fail("expected satisfiable ToNumber undefined goal"))

      val witness = Reifier
        .witness(solved, List(SolverTest.x))
        .getOrElse(fail("expected ToNumber undefined witness"))
      assert(witness(SolverTest.x) == "undefined")
    }

    check("ToLength delegates to ToIntegerOrInfinity via implications") {
      val toLength = SECall("ToLength", List(xSym))
      val inner = SECall("ToIntegerOrInfinity", List(xSym))
      val innerValue = SEField(inner, "Value")
      val retValue = SEField(toLength, "Value")
      val maxSafeLength =
        SELit(EMath(BigDecimal("9007199254740991")))
      val cases = RewriteRules.aoModel(toLength)

      assert(cases.size == 4)
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when == List(FTypeCheck(inner, AbruptT)) &&
            conclusion == List(FTypeCheck(toLength, ThrowT))
          case _ => false
        },
      )
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when.contains(FTypeCheck(inner, NormalT)) &&
            conclusion.contains(
              FEq(SEField(toLength, "Value"), SELit(ENumber(0.0))),
            )
          case _ => false
        },
      )
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when.contains(FLt(maxSafeLength, innerValue)) &&
            conclusion.contains(FEq(retValue, maxSafeLength))
          case _ => false
        },
      )
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when.contains(FLt(SELit(EMath(0)), innerValue)) &&
            conclusion == List(FTypeCheck(toLength, NormalT))
          case _ => false
        },
      )
      assert(!cases.exists {
        case FImply(_, conclusion) =>
          conclusion.contains(FEq(retValue, innerValue))
        case _ => false
      })
    }

    // DEFERRED(z3): the FLt bound sits on ToIntegerOrInfinity(x)["Value"]; the
    // solver does not bridge it onto `x` (no `Value = x`-style equality in the
    // truncating cases), so the reifier never sees an arg-rooted bound.
    // Re-enable once the solver (or Z3) projects bounds through the AO chain.
    /*
    checkParamWitness(
      "ToIntegerOrInfinity finite bounds reify through the input",
    )(
      {
        val toInteger = SECall("ToIntegerOrInfinity", List(xSym))
        val value = SEField(toInteger, "Value")
        List(
          FTypeCheck(toInteger, NormalT),
          FLt(value, SELit(EMath(0))),
          FNot(FEq(value, SELit(EInfinity(true)))),
          FNot(FEq(value, SELit(EInfinity(false)))),
        )
      },
    ) { js =>
      assert(js == "-1")
    }
     */

    // the reifier samples a witness from FLt bounds and point exclusions that
    // the type lattice cannot encode (Model.excluded / excludedTys / bounds)
    checkParamWitness("bounded number reify can choose fractional witness")(
      List(
        isType(xSym, NumberT),
        isNotValue(xSym, ENumber(-1.0)),
        isNotValue(xSym, ENumber(0.0)),
        isNotValue(xSym, ENumber(1.0)),
        FNot(FLt(SELit(ENumber(1.0)), xSym)),
        FNot(FLt(xSym, SELit(ENumber(-1.0)))),
      ),
    ) { js =>
      assert(js == "-0.5")
    }

    checkParamWitness("number reify respects NumberInt exclusion")(
      List(
        isType(xSym, NumberT),
        isNotType(xSym, NumberIntT),
        FNot(FLt(xSym, SELit(ENumber(1.0)))),
      ),
    ) { js =>
      assert(js == "1.5")
    }

    check("ToUint32 delegates to ToNumber via implications") {
      val toUint32 = SECall("ToUint32", List(xSym))
      val toNumber = SECall("ToNumber", List(xSym))
      val numVal = SEField(toNumber, "Value")
      val retValue = SEField(toUint32, "Value")
      val cases = RewriteRules.aoModel(toUint32)

      assert(cases.size == 7)
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when == List(FTypeCheck(toNumber, AbruptT)) &&
            conclusion == List(FTypeCheck(toUint32, ThrowT))
          case _ => false
        },
      )
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when.contains(FEq(numVal, SELit(ENumber(Double.NaN)))) &&
            conclusion.contains(FEq(retValue, SELit(ENumber(0.0))))
          case _ => false
        },
      )
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when == List(FTypeCheck(toNumber, NormalT)) &&
            conclusion == List(FTypeCheck(toUint32, NormalT))
          case _ => false
        },
      )
    }

    checkParamWitness("ToUint32 abrupt requirement reifies via ToNumber")(
      {
        val toUint32 = SECall("ToUint32", List(xSym))
        List(FTypeCheck(toUint32, AbruptT))
      },
    ) { js =>
      assert(js == "Symbol()" || js == "0n")
    }

    checkParamWitness(
      "LengthOfArrayLike non-zero goal reifies as length property",
    )(
      {
        val length = SECall("LengthOfArrayLike", List(xSym))
        val value = SEField(length, "Value")
        List(
          FTypeCheck(length, NormalT),
          FNot(FEq(value, SELit(ENumber(0.0)))),
        )
      },
    ) { js =>
      assert(js.contains("length"))
      assert(!js.contains("length: 0"))
    }

    check("CreateDataPropertyOrThrow delegates to DefineOwnProperty") {
      val createOrThrow = SECall(
        "CreateDataPropertyOrThrow",
        List(xSym, SELit(EStr("p")), ySym),
      )
      val create = SECall(
        "CreateDataProperty",
        List(xSym, SELit(EStr("p")), ySym),
      )
      val cases = RewriteRules.aoModel(createOrThrow)

      assert(cases.size == 3)
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when == List(FTypeCheck(create, AbruptT)) &&
            conclusion == List(FTypeCheck(createOrThrow, ThrowT))
          case _ => false
        },
      )
      assert(
        cases.exists {
          case FImply(when, conclusion) =>
            when.contains(FEq(SEField(create, "Value"), SELit(EBool(true)))) &&
            conclusion == List(FTypeCheck(createOrThrow, NormalT))
          case _ => false
        },
      )
    }

    checkParamWitness(
      "CreateDataPropertyOrThrow throw reifies as defineProperty trap",
    )(
      {
        val createOrThrow = SECall(
          "CreateDataPropertyOrThrow",
          List(xSym, SELit(EStr("p")), SELit(EMath(1))),
        )
        List(FTypeCheck(createOrThrow, ThrowT))
      },
    ) { js =>
      assert(js.contains("new Proxy("))
      assert(js.contains("defineProperty"))
    }

    checkParamWitness(
      "CreateDataPropertyOrThrow normal reifies as object-capable receiver",
    )(
      {
        val createOrThrow = SECall(
          "CreateDataPropertyOrThrow",
          List(xSym, SELit(EStr("p")), SELit(EMath(1))),
        )
        List(FTypeCheck(createOrThrow, NormalT))
      },
    ) { js =>
      assert(js.nonEmpty)
      assert(!js.contains("undefined"))
    }

    checkParamWitness("Get value projection reifies as property value")(
      List(
        isValue(
          SEField(SECall("Get", List(xSym, SELit(EStr("p")))), "Value"),
          EMath(1),
        ),
      ),
    ) { js =>
      assert(js.contains("p"))
      assert(js.contains("1"))
    }

    check("internal method trap cannot reify on undefined base") {
      val key = SEField(SEGlobal("SYMBOL"), SELit(EStr("iterator")))
      val get = SECall("Get", List(xSym, key))

      assert(
        solveAndReify(
          List(
            isType(xSym, UndefT),
            isType(get, NormalT),
            isType(SEField(get, "Value"), UndefT || NullT),
          ),
        ).isEmpty,
      )
    }

    checkParamWitness("Get returning nullish reifies as an ordinary object")(
      List(
        isType(
          SEField(
            SECall(
              "Get",
              List(xSym, SEField(SEGlobal("SYMBOL"), SELit(EStr("iterator")))),
            ),
            "Value",
          ),
          UndefT || NullT,
        ),
      ),
    ) { js =>
      // an ordinary object with a nullish @@iterator suffices (no Proxy needed)
      assert(js.contains("Symbol.iterator"))
      assert(js.contains("null") || js.contains("undefined"))
    }

    // reify-in-isolation: assuming the solver delivers the abrupt-call fact
    // (today stripCallFacts drops its GetMethod form), the reifier builds a
    // throwing @@iterator method on its own
    checkParamWitness("abrupt @@iterator call reifies as a throwing method")(
      {
        val key = SEField(SEGlobal("SYMBOL"), SELit(EStr("iterator")))
        val method = SEField(SECall("Get", List(xSym, key)), "Value")
        List(
          isType(xSym, ObjectT),
          isType(SECall("Get", List(xSym, key)), NormalT),
          isNotValue(method, EUndef()),
          isType(method, ObjectT),
          isType(SECall("Call", List(method, xSym)), AbruptT),
        )
      },
    ) { js =>
      assert(js.contains("Symbol.iterator"))
      assert(js.contains("throw"))
    }

    // reify-in-isolation: an abrupt property read becomes a throwing getter
    checkParamWitness("abrupt Get reifies as a throwing getter")(
      List(
        isType(xSym, ObjectT),
        isType(SECall("Get", List(xSym, SELit(EStr("flags")))), AbruptT),
      ),
    ) { js =>
      assert(js.contains("flags"))
      assert(js.contains("throw"))
    }

    checkParamWitness("HasProperty value projection reifies as property shape")(
      List(
        isValue(
          SEField(
            SECall("HasProperty", List(xSym, SELit(EStr("p")))),
            "Value",
          ),
          EBool(true),
        ),
      ),
    ) { js =>
      assert(js.contains("p"))
    }

    check("unknown internal field existence is not a JS property witness") {
      assert(solveAndReify(List(FExists(xSym, SELit(EStr("p"))))).isEmpty)
    }

    check("global refs are not treated as zero-argument applications") {
      val symIterator = SEField(SEGlobal("SYMBOL"), SELit(EStr("iterator")))
      val formula = isType(symIterator, SymbolT)

      assert(!Solver.hasUninterpretableApp(List(formula)))
      assert(Solver.outerAppNames(formula).isEmpty)
    }

    check("zero-argument applications remain uninterpretable calls") {
      val oldGlobalShape =
        SEField(SECall("SYMBOL", List()), SELit(EStr("iterator")))
      val formula = isType(oldGlobalShape, SymbolT)

      assert(Solver.hasUninterpretableApp(List(formula)))
      assert(Solver.outerAppNames(formula) == Set("SYMBOL"))
    }

    checkParamWitness("known internal field existence reifies by object shape")(
      List(FExists(xSym, SELit(EStr("TypedArrayName")))),
    ) { js =>
      assert(js.contains("Int8Array"))
      assert(!js.contains("TypedArrayName"))
    }

    checkParamWitness("internal field value reifies by object shape")(
      List(
        isValue(SEField(xSym, "TypedArrayName"), EStr("Int8Array")),
      ),
    ) { js =>
      assert(js.contains("Int8Array"))
      assert(!js.contains("TypedArrayName"))
    }

    checkParamWitness(
      "source text internal field reifies as ordinary function",
    )(
      List(
        FExists(xSym, SELit(EStr("SourceText"))),
        isType(SEField(xSym, "SourceText"), StrT),
      ),
    ) { js =>
      // [[Call]] without [[Construct]] -> arrow; an arrow is a valid
      // SourceText-bearing function, so either function form is acceptable
      assert(js.contains("=>") || js.contains("function"))
    }

    check(
      "negative source text record constraint keeps a plain object witness",
    ) {
      val witness = solveAndReify(
        List(
          isType(xSym, ObjectT),
          isNotType(xSym, RecordT("BuiltinFunctionObject")),
          FNot(FExists(xSym, SELit(EStr("SourceText")))),
        ),
      ).getOrElse(fail("expected plain object witness"))

      assert(witness(SolverTest.x).nonEmpty)
    }

    checkParamWitness("symbol description internal field reifies as symbol")(
      List(
        isType(xSym, SymbolT),
        isValue(SEField(xSym, "Description"), EUndef()),
      ),
    ) { js =>
      assert(js == "Symbol()")
    }

    checkParamWitness("revoked proxy internal slots reify via Proxy.revocable")(
      List(
        isType(xSym, RecordT("ProxyExoticObject")),
        isValue(SEField(xSym, "ProxyTarget"), ENull()),
      ),
    ) { js =>
      assert(js.contains("Proxy.revocable"))
      assert(js.contains(".revoke()"))
    }

    checkParamWitness("intrinsic equality reifies as builtin object")(
      {
        val iteratorPrototype = SEField(
          SEField(
            SEField(
              SEField(SEGlobal("EXECUTION_STACK"), SELit(EMath(0))),
              "Realm",
            ),
            "Intrinsics",
          ),
          "%Iterator.prototype%",
        )
        List(isType(xSym, ObjectT), FEq(xSym, iteratorPrototype))
      },
    ) { js =>
      assert(js == "Iterator.prototype")
    }

    checkParamWitness(
      "intrinsic inequality allows an ordinary object witness",
    )(
      {
        val iteratorPrototype = SEField(
          SEField(
            SEField(
              SEField(SEGlobal("EXECUTION_STACK"), SELit(EMath(0))),
              "Realm",
            ),
            "Intrinsics",
          ),
          "%Iterator.prototype%",
        )
        List(isType(xSym, ObjectT), FNot(FEq(xSym, iteratorPrototype)))
      },
    ) { js =>
      assert(js.nonEmpty)
      assert(js != "Iterator.prototype")
    }

    checkParamWitness(
      "intrinsic inequality with property descriptors reifies as ordinary object",
      params = List(SolverTest.x, SolverTest.y),
    )(
      {
        val iteratorPrototype = SEField(
          SEField(
            SEField(
              SEField(SEGlobal("EXECUTION_STACK"), SELit(EMath(0))),
              "Realm",
            ),
            "Intrinsics",
          ),
          "%Iterator.prototype%",
        )
        val key = SELit(EStr("constructor"))
        val getOwn = SECall("GetOwnProperty", List(xSym, xSym, key))
        val desc = SERecord(
          "PropertyDescriptor",
          Map(
            "Value" -> ySym,
            "Writable" -> SELit(EBool(true)),
            "Enumerable" -> SELit(EBool(true)),
            "Configurable" -> SELit(EBool(true)),
          ),
        )
        val define = SECall("DefineOwnProperty", List(xSym, xSym, key, desc))
        List(
          isType(xSym, ObjectT),
          FNot(FEq(xSym, iteratorPrototype)),
          isType(getOwn, NormalT),
          isValue(SEField(getOwn, "Value"), EUndef()),
          isType(define, NormalT),
          isValue(SEField(define, "Value"), EBool(true)),
        )
      },
    ) { js =>
      // an ordinary extensible object (no own "constructor") satisfies the
      // GetOwnProperty=undefined / DefineOwnProperty=true constraints
      assert(js != "Iterator.prototype")
      assert(js.contains("{"))
    }

    // DEFERRED(niche): an auto-length ([[ArrayLength]] == ~auto~) typed array is
    // a length-tracking view over a resizable ArrayBuffer
    // (new Int8Array(new ArrayBuffer(0, { maxByteLength: N }))). The reifier
    // emits a plain `new Int8Array()` for now; this exotic creation form is unbuilt.
    /*
    checkParamWitness(
      "auto-length typed array reifies as length-tracking view",
    )(
      List(
        FExists(xSym, SELit(EStr("TypedArrayName"))),
        isValue(SEField(xSym, "ArrayLength"), EEnum("auto")),
      ),
    ) { js =>
      assert(js.contains("new ArrayBuffer"))
      assert(js.contains("maxByteLength"))
    }
     */

    check("dynamic field access is not reified as a fixed internal field") {
      // a symbolic key cannot be pinned to a specific property, so the
      // constraint is left unapplied (x stays unconstrained) rather than
      // fabricating an internal field on x
      val w = solveAndReify(
        List(isValue(SEField(xSym, ySym), EStr("Int8Array"))),
        params = List(SolverTest.x, SolverTest.y),
      )
      assert(w.forall(!_(SolverTest.x).contains("Int8Array")))
    }

    check(
      "value-level Call projection is not stripped into the Call completion",
    ) {
      val call = SECall("Call", List(xSym, ySym))
      val value = SEField(call, "Value")
      val expanded = expand(List(isValue(value, EMath(1))))

      assert(expanded.contains(isValue(value, EMath(1))))
      assert(!expanded.contains(isValue(call, EMath(1))))
    }

    check("Completion-wrapped Call value projection is preserved") {
      val call = SECall("Call", List(xSym, ySym))
      val value = SEField(call, "Value")
      val wrappedValue =
        SEField(SECall("Completion", List(call)), "Value")
      val expanded = expand(List(isValue(wrappedValue, EMath(1))))

      assert(expanded.contains(isValue(value, EMath(1))))
      assert(!expanded.contains(isValue(call, EMath(1))))
    }

    check("unknown Completion value projection is preserved") {
      val wrappedValue =
        SEField(SECall("Completion", List(xSym)), "Value")
      val bareValue = SEField(xSym, "Value")
      val expanded = expand(List(isValue(wrappedValue, EMath(1))))

      assert(expanded.contains(isValue(wrappedValue, EMath(1))))
      assert(!expanded.contains(isValue(bareValue, EMath(1))))
      assert(!expanded.contains(isValue(xSym, EMath(1))))
    }

    check("NormalCompletion value projection rewrites to inner value") {
      val wrappedValue =
        SEField(SECall("NormalCompletion", List(xSym)), "Value")
      val expanded = expand(List(isValue(wrappedValue, EMath(1))))

      assert(expanded.contains(isValue(xSym, EMath(1))))
      assert(!expanded.contains(isValue(wrappedValue, EMath(1))))
    }

    checkParamWitness(
      "concrete IteratorRecord type check does not block reify",
    )(
      List(
        isType(xSym, ObjectT),
        isType(SECall("Get", List(xSym, SELit(EStr("next")))), NormalT),
        isType(
          SERecord(
            "IteratorRecord",
            Map(
              "Iterator" -> xSym,
              "NextMethod" -> SEField(
                SECall("Get", List(xSym, SELit(EStr("next")))),
                "Value",
              ),
              "Done" -> SELit(EBool(false)),
            ),
          ),
          RecordT("IteratorRecord"),
        ),
      ),
    ) { js =>
      assert(js.nonEmpty)
    }

    checkParamWitness(
      "iterator next method call facts reify through property value",
    )(
      {
        val getNext = SECall("Get", List(xSym, SELit(EStr("next"))))
        val nextMethod = SEField(getNext, "Value")
        val callNext = SECall("Call", List(nextMethod, xSym))
        List(
          isType(xSym, ObjectT),
          isType(getNext, NormalT),
          isType(
            SERecord(
              "IteratorRecord",
              Map(
                "Iterator" -> xSym,
                "NextMethod" -> nextMethod,
                "Done" -> SELit(EBool(false)),
              ),
            ),
            RecordT("IteratorRecord"),
          ),
          isType(callNext, NormalT),
          isType(SEField(callNext, "Value"), ObjectT),
        )
      },
    ) { js =>
      // a finite iterator: x.next is a stateful function that yields once then
      // reports done (exact spacing / explicit done:false are not load-bearing)
      assert(js.contains("next"))
      assert(js.contains("i++")) // stateful counter: yields then terminates
      assert(js.contains("done: true")) // eventually reports done
    }

    check("nested solver-only calls are dropped without direct projection") {
      val toObject = SECall("ToObject", List(xSym))
      val objectValue = SEField(toObject, "Value")
      val get = SECall("Get", List(objectValue, SELit(EStr("p"))))
      val propertyFact = isValue(SEField(get, "Value"), EMath(1))
      val solved = solver
        .solve(List(isType(toObject, NormalT), propertyFact))
        .getOrElse(fail("expected satisfiable ToObject goal"))

      assert(!solved.contains(propertyFact))
      assert(!solved.contains(isType(toObject, NormalT)))
    }

    check("ToNumber abrupt requirement selects compatible throwing case") {
      val toNumber = SECall("ToNumber", List(xSym))
      val solved = solver
        .solve(List(isType(toNumber, AbruptT)))
        .getOrElse(fail("expected satisfiable ToNumber goal"))

      assert(solved.contains(isType(xSym, SymbolT || BigIntT)))
      assert(!solved.exists(_.toString.contains("ToNumber")))
    }

    check("ToNumber throwing summary fires when its premise is known") {
      val toNumber = SECall("ToNumber", List(xSym))
      val solved = solver
        .solve(List(isType(xSym, SymbolT), isType(toNumber, AbruptT)))
        .getOrElse(fail("expected satisfiable ToNumber goal"))

      assert(solved.contains(isType(xSym, SymbolT)))
      assert(!solved.exists(_.toString.contains("ToNumber")))
    }

    check("unknown Completion Type check stays on wrapper") {
      val wrapped = SECall("Completion", List(xSym))
      val typeCheck =
        FEq(SEField(wrapped, "Type"), SELit(EEnum("normal")))
      val expanded = expand(List(typeCheck))

      assert(expanded.contains(isType(wrapped, NormalT)))
      assert(!expanded.contains(isType(xSym, NormalT)))
    }

    check("NormalCompletion Type check rewrites as known normal") {
      val wrapped = SECall("NormalCompletion", List(xSym))
      val typeCheck =
        FEq(SEField(wrapped, "Type"), SELit(EEnum("normal")))
      val expanded = expand(List(typeCheck))

      assert(expanded.isEmpty)
    }

    check("IteratorComplete reads done from IteratorNext value") {
      val iterRecord = SERecord(
        "IteratorRecord",
        Map(
          "Iterator" -> xSym,
          "NextMethod" -> ySym,
          "Done" -> SELit(EBool(false)),
        ),
      )
      val call = SECall("Call", List(ySym, xSym))
      val value = SEField(call, "Value")
      val done = SECall("Get", List(value, SELit(EStr("done"))))
      val bareDone = SECall("Get", List(call, SELit(EStr("done"))))
      val model =
        RewriteRules.aoModel(
          SECall(
            "IteratorComplete",
            List(SECall("IteratorNext", List(iterRecord))),
          ),
        )

      assert(
        model.exists {
          case FImply(when, _) => when.contains(isType(done, NormalT))
          case _               => false
        },
      )
      assert(
        !model.exists {
          case FImply(when, conclusion) =>
            (when ++ conclusion).contains(isType(bareDone, NormalT))
          case _ => false
        },
      )
    }

    check("IteratorValue reads value from IteratorNext value") {
      val iterRecord = SERecord(
        "IteratorRecord",
        Map(
          "Iterator" -> xSym,
          "NextMethod" -> ySym,
          "Done" -> SELit(EBool(false)),
        ),
      )
      val call = SECall("Call", List(ySym, xSym))
      val value = SEField(call, "Value")
      val resultValue = SECall("Get", List(value, SELit(EStr("value"))))
      val bareValue = SECall("Get", List(call, SELit(EStr("value"))))
      val model =
        RewriteRules.aoModel(
          SECall(
            "IteratorValue",
            List(SECall("IteratorNext", List(iterRecord))),
          ),
        )

      assert(
        model.exists {
          case FImply(when, _) => when.contains(isType(resultValue, NormalT))
          case _               => false
        },
      )
      assert(
        !model.exists {
          case FImply(when, conclusion) =>
            (when ++ conclusion).contains(isType(bareValue, NormalT))
          case _ => false
        },
      )
    }

    check("symbolic interpreter explores both disjunctive path constraints") {
      val xLocal = Name("x")
      val yLocal = Name("y")
      val xExpr = ERef(xLocal)
      val yExpr = ERef(yLocal)
      val guard = Branch(
        0,
        BranchKind.If,
        EBinary(
          BOp.Or,
          EBinary(BOp.Eq, xExpr, EMath(BigDecimal(0))),
          EBinary(BOp.Eq, xExpr, EMath(BigDecimal(1))),
        ),
      )
      val target = Branch(
        1,
        BranchKind.If,
        EBinary(BOp.Eq, yExpr, EMath(BigDecimal(2))),
      )
      guard.thenNode = Some(target)
      val irFunc = Func(
        true,
        FuncKind.AbsOp,
        "dnf",
        List(
          Param(xLocal, Type(NumberT), false),
          Param(yLocal, Type(NumberT), false),
        ),
        Type(NormalT),
        INop(),
      )
      val func = CFGFunc(0, irFunc, guard)
      val cfg = CFG(List(func))
      given CFG = cfg
      val localSolver = Solver()

      val goals =
        SymbolicInterpreter(
          func,
          Cond(target, true),
          localSolver.solveAll,
        ).result
          .take(3)
          .toList
      val expected = Set(
        List(
          isValue(SESym(Sym.Arg(0)), EMath(BigDecimal(0))),
          isValue(SESym(Sym.Arg(1)), EMath(BigDecimal(2))),
        ),
        List(
          isValue(SESym(Sym.Arg(0)), EMath(BigDecimal(1))),
          isValue(SESym(Sym.Arg(1)), EMath(BigDecimal(2))),
        ),
      )

      assert(goals.size == 2)
      assert(goals.toSet == expected)
    }

    check("symbolic interpreter respects back pop from local lists") {
      val xsLocal = Name("xs")
      val yLocal = Name("y")
      val target = Branch(
        1,
        BranchKind.If,
        EBinary(BOp.Eq, ERef(yLocal), EMath(BigDecimal(2))),
      )
      val entry = Block(
        0,
        scala.collection.mutable.ListBuffer(
          ILet(
            xsLocal,
            EList(List(EMath(BigDecimal(1)), EMath(BigDecimal(2)))),
          ),
          IPop(yLocal, ERef(xsLocal), front = false),
        ),
        Some(target),
      )
      val irFunc = Func(
        true,
        FuncKind.AbsOp,
        "backPop",
        Nil,
        Type(NormalT),
        INop(),
      )
      val func = CFGFunc(0, irFunc, entry)
      val cfg = CFG(List(func))
      given CFG = cfg
      val localSolver = Solver()

      val goals =
        SymbolicInterpreter(
          func,
          Cond(target, true),
          localSolver.solveAll,
        ).result.toList

      assert(goals == List(Nil))
    }

  }

  init
}
