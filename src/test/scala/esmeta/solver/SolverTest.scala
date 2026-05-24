package esmeta.solver

import esmeta.ESMetaTest
import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*, Sym.*

class SolverTest extends ESMetaTest {
  val name = "solverTest"
  val category = "solver"

  private def solveAndReify(
    goal: Goal,
    params: List[Sym],
  ): Option[Witness] =
    Solver.solve(goal).flatMap(Reify(_, params).witness)

  def init: Unit = {
    // --- literal equality ---
    check("literal equality: x == 0") {
      val goal = List(FEq(SESym(Arg(0)), SELit(EMath(0))))
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result == Some(Map(Arg(0) -> "0")))
    }

    check("literal equality: x == NaN") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(NumberT)),
        FEq(SESym(Arg(0)), SELit(ENumber(Double.NaN))),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.get(Arg(0)) == "NaN")
    }

    check("literal equality: x == \"hello\"") {
      val goal = List(FEq(SESym(Arg(0)), SELit(EStr("hello"))))
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result == Some(Map(Arg(0) -> "\"hello\"")))
    }

    // --- type narrowing ---
    check("type narrowing: x ∈ Object") {
      val goal = List(FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT)))
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.get(Arg(0)) == "{}")
    }

    check("type narrowing: x ∈ String") {
      val goal = List(FEq(SETypeOf(SESym(Arg(0))), SEType(StrT)))
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.get(Arg(0)) == "\"\"")
    }

    check("type narrowing: x ∈ Function") {
      val goal = List(FEq(SETypeOf(SESym(Arg(0))), SEType(FunctionT)))
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.get(Arg(0)) == "() => {}")
    }

    // --- type exclusion ---
    check("type exclusion: x ∉ Object") {
      val goal = List(FNot(FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT))))
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)) != "{}")
    }

    check("type exclusion: union survives partial negation") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(NumberT || StrT)),
        FNot(FEq(SETypeOf(SESym(Arg(0))), SEType(NumberT))),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result == Some(Map(Arg(0) -> "\"\"")))
    }

    // --- inequality ---
    check("inequality: x != null") {
      val goal = List(FNot(FEq(SESym(Arg(0)), SELit(ENull()))))
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)) != "null")
    }

    check("inequality: x != undefined") {
      val goal = List(FNot(FEq(SESym(Arg(0)), SELit(EUndef()))))
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)) != "undefined")
    }

    // --- property constraints ---
    check("property: Get(x, \"name\") == \"foo\"") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT)),
        FEq(
          SEApp("Get", List(SESym(Arg(0)), SELit(EStr("name")))),
          SELit(EStr("foo")),
        ),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("name: \"foo\""))
    }

    check("property: Get(x, \"value\") ∈ Abrupt") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT)),
        FEq(
          SETypeOf(SEApp("Get", List(SESym(Arg(0)), SELit(EStr("value"))))),
          SEType(AbruptT),
        ),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("get value() { throw 0; }"))
    }

    check("property: HasProperty(x, \"foo\") == true") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT)),
        FEq(
          SEApp("HasProperty", List(SESym(Arg(0)), SELit(EStr("foo")))),
          SELit(EBool(true)),
        ),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("foo"))
    }

    // --- object config ---
    check("config: IsExtensible(x) == false") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT)),
        FEq(SEApp("IsExtensible", List(SESym(Arg(0)))), SELit(EBool(false))),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("Object.preventExtensions"))
    }

    check("config: GetPrototypeOf(x) == null") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT)),
        FEq(SEApp("GetPrototypeOf", List(SESym(Arg(0)))), SELit(ENull())),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("Object.create(null)"))
    }

    // --- proxy ---
    check("proxy: PreventExtensions(x) == false") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT)),
        FEq(
          SEApp("PreventExtensions", List(SESym(Arg(0)))),
          SELit(EBool(false)),
        ),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("new Proxy"))
    }

    check("proxy: Call(x) ∈ Abrupt") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(FunctionT)),
        FEq(SETypeOf(SEApp("Call", List(SESym(Arg(0))))), SEType(AbruptT)),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("new Proxy"))
    }

    // --- composition ---
    check("composed: Get normal + Get abrupt on same object") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT)),
        FEq(
          SEApp("Get", List(SESym(Arg(0)), SELit(EStr("name")))),
          SELit(EUndef()),
        ),
        FEq(
          SETypeOf(SEApp("Get", List(SESym(Arg(0)), SELit(EStr("message"))))),
          SEType(AbruptT),
        ),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      val js = result.get(Arg(0))
      assert(js.contains("name: undefined"))
      assert(js.contains("get message() { throw 0; }"))
    }

    // --- contradiction ---
    check("contradiction: x == 0 ∧ x == 1 → None") {
      val goal = List(
        FEq(SESym(Arg(0)), SELit(EMath(0))),
        FEq(SESym(Arg(0)), SELit(EMath(1))),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isEmpty)
    }

    check("contradiction: x == x ∧ NOT(x == x) → None") {
      val goal = List(
        FEq(SESym(Arg(0)), SESym(Arg(0))),
        FNot(FEq(SESym(Arg(0)), SESym(Arg(0)))),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isEmpty)
    }

    // --- completion normalization ---
    check("completion: NOT(Normal) normalized to Abrupt") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT)),
        FNot(
          FEq(
            SETypeOf(SEApp("Get", List(SESym(Arg(0)), SELit(EStr("key"))))),
            SEType(NormalT),
          ),
        ),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("get key() { throw 0; }"))
    }

    // --- multi-param ---
    check("multi-param: x == 0, y ∈ Object") {
      val goal = List(
        FEq(SESym(Arg(0)), SELit(EMath(0))),
        FEq(SETypeOf(SESym(Arg(1))), SEType(ObjectT)),
      )
      val result = solveAndReify(goal, List(Arg(0), Arg(1)))
      assert(result.isDefined)
      assert(result.get(Arg(0)) == "0")
      assert(result.get(Arg(1)) == "{}")
    }

    // --- normal completion stripping ---
    check("normal completion on internal method is default — stripped") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(ObjectT)),
        FEq(
          SETypeOf(SEApp("Get", List(SESym(Arg(0)), SELit(EStr("a"))))),
          SEType(NormalT),
        ),
      )
      val result = solveAndReify(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)) == "{}")
    }

    check("rewrite: ToBoolean(false) == true is contradiction") {
      val goal = List(
        FEq(SEApp("ToBoolean", List(SELit(EBool(false)))), SELit(EBool(true))),
      )
      assert(Solver.solve(goal).isEmpty)
    }

    check("rewrite: literal-left predicate equality is canonicalized") {
      val goal = List(
        FEq(SETypeOf(SESym(Arg(0))), SEType(NumberT)),
        FEq(SELit(EBool(true)), SEApp("IsCallable", List(SESym(Arg(0))))),
      )
      assert(Solver.solve(goal).isEmpty)
    }
  }

  init
}
