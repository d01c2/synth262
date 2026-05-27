package esmeta.solver

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

    check("GetIterator normal keeps Call completion separate from its value") {
      val methodResult = SEApp("Get", List(xSym, SELit(EStr("iterator"))))
      val method = SEProj(methodResult, SELit(EStr("Value")))
      val call = SEApp("Call", List(method, xSym))
      val value = SEProj(call, SELit(EStr("Value")))
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
      val value = SEProj(call, SELit(EStr("Value")))
      val rewritten =
        rewrite(
          List(isType(SEApp("IteratorNext", List(iterRecord)), NormalT)),
        )

      assert(rewritten.contains(isType(call, NormalT)))
      assert(rewritten.contains(isType(value, ObjectT)))
      assert(!rewritten.contains(isType(call, ObjectT)))
    }

    check("ToNumber value projection rewrites as a numeric input constraint") {
      val value =
        SEProj(SEApp("ToNumber", List(xSym)), SELit(EStr("Value")))
      val rewritten = rewrite(List(isValue(value, EMath(1))))

      assert(rewritten.contains(isValue(xSym, EMath(1))))
      assert(rewritten.contains(isType(xSym, NumberT)))
      assert(!rewritten.contains(isValue(value, EMath(1))))
    }

    check("ToNumber value projection type rewrites to the input type") {
      val value =
        SEProj(SEApp("ToNumber", List(xSym)), SELit(EStr("Value")))
      val rewritten = rewrite(List(isType(value, NumberIntT)))

      assert(rewritten.contains(isType(xSym, NumberIntT)))
      assert(!rewritten.contains(isType(value, NumberIntT)))
    }

    check("ToLength value projection delegates to ToNumber before rewriting") {
      val value =
        SEProj(SEApp("ToLength", List(xSym)), SELit(EStr("Value")))
      val rewritten = rewrite(List(FLt(value, SELit(EMath(0)))))

      assert(rewritten.contains(FLt(xSym, SELit(EMath(0)))))
      assert(rewritten.contains(isType(xSym, NumberT)))
      assert(!rewritten.contains(FLt(value, SELit(EMath(0)))))
    }

    checkParamWitness("Get value projection reifies as property value")(
      List(
        isValue(
          SEProj(
            SEApp("Get", List(xSym, SELit(EStr("p")))),
            SELit(EStr("Value")),
          ),
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
          SEProj(
            SEApp("HasProperty", List(xSym, SELit(EStr("p")))),
            SELit(EStr("Value")),
          ),
          EBool(true),
        ),
      ),
    ) { js =>
      assert(js.contains("p"))
    }

    check(
      "value-level Call projection is not stripped into the Call completion",
    ) {
      val call = SEApp("Call", List(xSym, ySym))
      val value = SEProj(call, SELit(EStr("Value")))
      val rewritten = rewrite(List(isValue(value, EMath(1))))

      assert(rewritten.contains(isValue(value, EMath(1))))
      assert(!rewritten.contains(isValue(call, EMath(1))))
    }

    check("Completion-wrapped Call value projection is preserved") {
      val call = SEApp("Call", List(xSym, ySym))
      val value = SEProj(call, SELit(EStr("Value")))
      val wrappedValue =
        SEProj(SEApp("Completion", List(call)), SELit(EStr("Value")))
      val rewritten = rewrite(List(isValue(wrappedValue, EMath(1))))

      assert(rewritten.contains(isValue(value, EMath(1))))
      assert(!rewritten.contains(isValue(call, EMath(1))))
    }

    check("unknown Completion value projection is preserved") {
      val wrappedValue =
        SEProj(SEApp("Completion", List(xSym)), SELit(EStr("Value")))
      val bareValue = SEProj(xSym, SELit(EStr("Value")))
      val rewritten = rewrite(List(isValue(wrappedValue, EMath(1))))

      assert(rewritten.contains(isValue(wrappedValue, EMath(1))))
      assert(!rewritten.contains(isValue(bareValue, EMath(1))))
      assert(!rewritten.contains(isValue(xSym, EMath(1))))
    }

    check("NormalCompletion value projection rewrites to inner value") {
      val wrappedValue =
        SEProj(SEApp("NormalCompletion", List(xSym)), SELit(EStr("Value")))
      val rewritten = rewrite(List(isValue(wrappedValue, EMath(1))))

      assert(rewritten.contains(isValue(xSym, EMath(1))))
      assert(!rewritten.contains(isValue(wrappedValue, EMath(1))))
    }

    check("Completion-wrapped ToNumber projection rewrites through value") {
      val toNumber = SEApp("ToNumber", List(xSym))
      val wrappedValue =
        SEProj(SEApp("Completion", List(toNumber)), SELit(EStr("Value")))
      val rewritten = rewrite(List(isValue(wrappedValue, EMath(1))))

      assert(rewritten.contains(isValue(xSym, EMath(1))))
      assert(rewritten.contains(isType(xSym, NumberT)))
      assert(!rewritten.contains(isValue(wrappedValue, EMath(1))))
    }

    check("unknown Completion Type check stays on wrapper") {
      val wrapped = SEApp("Completion", List(xSym))
      val typeCheck =
        FEq(SEProj(wrapped, SELit(EStr("Type"))), SELit(EEnum("normal")))
      val rewritten = rewrite(List(typeCheck))

      assert(rewritten.contains(isType(wrapped, NormalT)))
      assert(!rewritten.contains(isType(xSym, NormalT)))
    }

    check("NormalCompletion Type check rewrites as known normal") {
      val wrapped = SEApp("NormalCompletion", List(xSym))
      val typeCheck =
        FEq(SEProj(wrapped, SELit(EStr("Type"))), SELit(EEnum("normal")))
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
      val value = SEProj(call, SELit(EStr("Value")))
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
      val value = SEProj(call, SELit(EStr("Value")))
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
  }

  init
}
