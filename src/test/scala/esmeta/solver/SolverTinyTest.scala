package esmeta.solver

import esmeta.cfg.{Branch, BranchKind, CFG, Func as CFGFunc}
import esmeta.es.util.Coverage.Cond
import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*

/** basic solver test */
class SolverTinyTest extends SolverTest {
  val name: String = "solverTinyTest"
  private def rewrite(goal: Goal): Goal = Solver.rewrite(goal)

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

    check("GetIterator normal keeps Call completion separate from its value") {
      val methodResult = SEApp("Get", List(xSym, SELit(EStr("iterator"))))
      val method = SEField(methodResult, "Value")
      val call = SEApp("Call", List(method, xSym))
      val value = SEField(call, "Value")
      val rewritten =
        rewrite(List(isType(SEApp("GetIterator", List(xSym)), NormalT)))

      assert(rewritten.contains(isType(methodResult, NormalT)))
      assert(rewritten.contains(isType(call, NormalT)))
      assert(rewritten.contains(isType(value, ObjectT)))
      assert(!rewritten.contains(isType(call, ObjectT)))
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
      val call = SEApp("Call", List(ySym, xSym))
      val value = SEField(call, "Value")
      val rewritten =
        rewrite(
          List(isType(SEApp("IteratorNext", List(iterRecord)), NormalT)),
        )

      assert(rewritten.contains(isType(call, NormalT)))
      assert(rewritten.contains(isType(value, ObjectT)))
      assert(!rewritten.contains(isType(call, ObjectT)))
    }

    check("ToNumber value projection is not rewritten into its input") {
      val value =
        SEField(SEApp("ToNumber", List(xSym)), "Value")
      val rewritten = rewrite(List(isValue(value, EMath(1))))

      assert(rewritten.contains(isValue(value, EMath(1))))
      assert(!rewritten.contains(isValue(xSym, EMath(1))))
      assert(!rewritten.contains(isType(xSym, NumberT)))
    }

    check("ToNumber model has six point-wise cases") {
      val toNumber = SEApp("ToNumber", List(xSym))
      val value = SEField(toNumber, "Value")
      val cases = RewriteRules.aoModel(toNumber)

      assert(cases.size == 6)
      assert(
        cases.exists(c =>
          c.when == List(isType(xSym, NumberT)) &&
          c.thenF == List(isType(toNumber, NormalT), FEq(value, xSym)),
        ),
      )
      assert(
        cases.exists(c =>
          c.when == List(isType(xSym, UndefT)) &&
          c.thenF == List(
            isType(toNumber, NormalT),
            FEq(value, SELit(ENumber(Double.NaN))),
          ),
        ),
      )
    }

    check("ToNumber value requirement is solved by implication cases") {
      val toNumber = SEApp("ToNumber", List(xSym))
      val solved = Solver
        .solve(List(isValue(SEField(toNumber, "Value"), ENumber(1.0))))
        .getOrElse(fail("expected satisfiable ToNumber goal"))

      assert(solved.contains(isType(xSym, NumberT)))
      assert(solved.contains(isValue(xSym, ENumber(1.0))))
      assert(!solved.exists(_.toString.contains("ToNumber")))
    }

    check("ToNumber model does not activate from input-only constraints") {
      val solved = Solver
        .solve(List(isType(xSym, NumberT)))
        .getOrElse(fail("expected satisfiable input-only goal"))

      assert(solved == List(isType(xSym, NumberT)))
    }

    check("ToNumber undefined can satisfy a NaN result") {
      val toNumber = SEApp("ToNumber", List(xSym))
      val solved = Solver
        .solve(
          List(
            isType(xSym, UndefT),
            isValue(SEField(toNumber, "Value"), ENumber(Double.NaN)),
          ),
        )
        .getOrElse(fail("expected satisfiable ToNumber undefined goal"))

      val witness =
        Reify(solved, List(SolverTest.x)).witness
          .getOrElse(fail("expected ToNumber undefined witness"))
      assert(witness(SolverTest.x) == "undefined")
    }

    check("ToLength value projection delegates to ToNumber before rewriting") {
      val value =
        SEField(SEApp("ToLength", List(xSym)), "Value")
      val rewritten = rewrite(List(FLt(value, SELit(EMath(0)))))

      assert(
        rewritten.contains(
          FLt(
            SEField(SEApp("ToNumber", List(xSym)), "Value"),
            SELit(EMath(0)),
          ),
        ),
      )
      assert(!rewritten.contains(FLt(xSym, SELit(EMath(0)))))
    }

    checkParamWitness("Get value projection reifies as property value")(
      List(
        isValue(
          SEField(SEApp("Get", List(xSym, SELit(EStr("p")))), "Value"),
          EMath(1),
        ),
      ),
    ) { js =>
      assert(js.contains("p"))
      assert(js.contains("1"))
    }

    checkParamWitness("HasProperty value projection reifies as property shape")(
      List(
        isValue(
          SEField(
            SEApp("HasProperty", List(xSym, SELit(EStr("p")))),
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

    check("generic projection is not an internal field witness") {
      assert(
        solveAndReify(
          List(
            isValue(
              SEProj(xSym, SELit(EStr("TypedArrayName"))),
              EStr("Int8Array"),
            ),
          ),
        ).isEmpty,
      )
    }

    check(
      "value-level Call projection is not stripped into the Call completion",
    ) {
      val call = SEApp("Call", List(xSym, ySym))
      val value = SEField(call, "Value")
      val rewritten = rewrite(List(isValue(value, EMath(1))))

      assert(rewritten.contains(isValue(value, EMath(1))))
      assert(!rewritten.contains(isValue(call, EMath(1))))
    }

    check("Completion-wrapped Call value projection is preserved") {
      val call = SEApp("Call", List(xSym, ySym))
      val value = SEField(call, "Value")
      val wrappedValue =
        SEField(SEApp("Completion", List(call)), "Value")
      val rewritten = rewrite(List(isValue(wrappedValue, EMath(1))))

      assert(rewritten.contains(isValue(value, EMath(1))))
      assert(!rewritten.contains(isValue(call, EMath(1))))
    }

    check("unknown Completion value projection is preserved") {
      val wrappedValue =
        SEField(SEApp("Completion", List(xSym)), "Value")
      val bareValue = SEField(xSym, "Value")
      val rewritten = rewrite(List(isValue(wrappedValue, EMath(1))))

      assert(rewritten.contains(isValue(wrappedValue, EMath(1))))
      assert(!rewritten.contains(isValue(bareValue, EMath(1))))
      assert(!rewritten.contains(isValue(xSym, EMath(1))))
    }

    check("NormalCompletion value projection rewrites to inner value") {
      val wrappedValue =
        SEField(SEApp("NormalCompletion", List(xSym)), "Value")
      val rewritten = rewrite(List(isValue(wrappedValue, EMath(1))))

      assert(rewritten.contains(isValue(xSym, EMath(1))))
      assert(!rewritten.contains(isValue(wrappedValue, EMath(1))))
    }

    check("ToNumber abrupt requirement selects throwing implication case") {
      val toNumber = SEApp("ToNumber", List(xSym))
      val solved = Solver
        .solve(List(isType(toNumber, AbruptT)))
        .getOrElse(fail("expected satisfiable ToNumber goal"))

      assert(solved.contains(isType(xSym, SymbolT || BigIntT)))
      assert(!solved.exists(_.toString.contains("ToNumber")))
    }

    check("unknown Completion Type check stays on wrapper") {
      val wrapped = SEApp("Completion", List(xSym))
      val typeCheck =
        FEq(SEField(wrapped, "Type"), SELit(EEnum("normal")))
      val rewritten = rewrite(List(typeCheck))

      assert(rewritten.contains(isType(wrapped, NormalT)))
      assert(!rewritten.contains(isType(xSym, NormalT)))
    }

    check("NormalCompletion Type check rewrites as known normal") {
      val wrapped = SEApp("NormalCompletion", List(xSym))
      val typeCheck =
        FEq(SEField(wrapped, "Type"), SELit(EEnum("normal")))
      val rewritten = rewrite(List(typeCheck))

      assert(rewritten.isEmpty)
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
      val call = SEApp("Call", List(ySym, xSym))
      val value = SEField(call, "Value")
      val done = SEApp("Get", List(value, SELit(EStr("done"))))
      val bareDone = SEApp("Get", List(call, SELit(EStr("done"))))
      val rewritten =
        rewrite(
          List(
            isType(
              SEApp(
                "IteratorComplete",
                List(SEApp("IteratorNext", List(iterRecord))),
              ),
              NormalT,
            ),
          ),
        )

      assert(rewritten.contains(isType(done, NormalT)))
      assert(!rewritten.contains(isType(bareDone, NormalT)))
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
      val call = SEApp("Call", List(ySym, xSym))
      val value = SEField(call, "Value")
      val resultValue = SEApp("Get", List(value, SELit(EStr("value"))))
      val bareValue = SEApp("Get", List(call, SELit(EStr("value"))))
      val rewritten =
        rewrite(
          List(
            isType(
              SEApp(
                "IteratorValue",
                List(SEApp("IteratorNext", List(iterRecord))),
              ),
              NormalT,
            ),
          ),
        )

      assert(rewritten.contains(isType(resultValue, NormalT)))
      assert(!rewritten.contains(isType(bareValue, NormalT)))
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

      val goals =
        SymbolicInterpreter(func, Cond(target, true), Solver.solveAll).result
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

  }

  init
}
