package esmeta.solver

import esmeta.ESMetaTest
import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*, SymId.*

class SolverTest extends ESMetaTest {
  val name = "solverTest"
  val category = "solver"

  def init: Unit = {
    // --- literal equality ---
    check("literal equality: x == 0") {
      val goal = List(FEq(Sym(Arg(0)), Lit(EMath(0))))
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result == Some(Map(Arg(0) -> "0")))
    }

    check("literal equality: x == NaN") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(NumberT)),
        FEq(Sym(Arg(0)), Lit(ENumber(Double.NaN))),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.get(Arg(0)) == "NaN")
    }

    check("literal equality: x == \"hello\"") {
      val goal = List(FEq(Sym(Arg(0)), Lit(EStr("hello"))))
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result == Some(Map(Arg(0) -> "\"hello\"")))
    }

    // --- type narrowing ---
    check("type narrowing: x ∈ Object") {
      val goal = List(FEq(TypeOf(Sym(Arg(0))), SType(ObjectT)))
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.get(Arg(0)) == "{}")
    }

    check("type narrowing: x ∈ String") {
      val goal = List(FEq(TypeOf(Sym(Arg(0))), SType(StrT)))
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.get(Arg(0)) == "\"\"")
    }

    check("type narrowing: x ∈ Function") {
      val goal = List(FEq(TypeOf(Sym(Arg(0))), SType(FunctionT)))
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.get(Arg(0)) == "() => {}")
    }

    // --- type exclusion ---
    check("type exclusion: x ∉ Object") {
      val goal = List(FNot(FEq(TypeOf(Sym(Arg(0))), SType(ObjectT))))
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)) != "{}")
    }

    // --- inequality ---
    check("inequality: x != null") {
      val goal = List(FNot(FEq(Sym(Arg(0)), Lit(ENull()))))
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)) != "null")
    }

    check("inequality: x != undefined") {
      val goal = List(FNot(FEq(Sym(Arg(0)), Lit(EUndef()))))
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)) != "undefined")
    }

    // --- property constraints ---
    check("property: Get(x, \"name\") == \"foo\"") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(ObjectT)),
        FEq(
          App("Get", List(Sym(Arg(0)), Lit(EStr("name")))),
          Lit(EStr("foo")),
        ),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("name: \"foo\""))
    }

    check("property: Get(x, \"value\") ∈ Abrupt") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(ObjectT)),
        FEq(
          TypeOf(App("Get", List(Sym(Arg(0)), Lit(EStr("value"))))),
          SType(AbruptT),
        ),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("get value() { throw 0; }"))
    }

    check("property: HasProperty(x, \"foo\") == true") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(ObjectT)),
        FEq(
          App("HasProperty", List(Sym(Arg(0)), Lit(EStr("foo")))),
          Lit(EBool(true)),
        ),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("foo"))
    }

    // --- object config ---
    check("config: IsExtensible(x) == false") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(ObjectT)),
        FEq(App("IsExtensible", List(Sym(Arg(0)))), Lit(EBool(false))),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("Object.preventExtensions"))
    }

    check("config: GetPrototypeOf(x) == null") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(ObjectT)),
        FEq(App("GetPrototypeOf", List(Sym(Arg(0)))), Lit(ENull())),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("Object.create(null)"))
    }

    // --- proxy ---
    check("proxy: PreventExtensions(x) == false") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(ObjectT)),
        FEq(
          App("PreventExtensions", List(Sym(Arg(0)))),
          Lit(EBool(false)),
        ),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("new Proxy"))
    }

    check("proxy: Call(x) ∈ Abrupt") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(FunctionT)),
        FEq(TypeOf(App("Call", List(Sym(Arg(0))))), SType(AbruptT)),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("new Proxy"))
    }

    // --- composition ---
    check("composed: Get normal + Get abrupt on same object") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(ObjectT)),
        FEq(
          App("Get", List(Sym(Arg(0)), Lit(EStr("name")))),
          Lit(EUndef()),
        ),
        FEq(
          TypeOf(App("Get", List(Sym(Arg(0)), Lit(EStr("message"))))),
          SType(AbruptT),
        ),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      val js = result.get(Arg(0))
      assert(js.contains("name: undefined"))
      assert(js.contains("get message() { throw 0; }"))
    }

    // --- contradiction ---
    check("contradiction: x == 0 ∧ x == 1 → None") {
      val goal = List(
        FEq(Sym(Arg(0)), Lit(EMath(0))),
        FEq(Sym(Arg(0)), Lit(EMath(1))),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isEmpty)
    }

    check("contradiction: x == x ∧ NOT(x == x) → None") {
      val goal = List(
        FEq(Sym(Arg(0)), Sym(Arg(0))),
        FNot(FEq(Sym(Arg(0)), Sym(Arg(0)))),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isEmpty)
    }

    // --- completion normalization ---
    check("completion: NOT(Normal) normalized to Abrupt") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(ObjectT)),
        FNot(
          FEq(
            TypeOf(App("Get", List(Sym(Arg(0)), Lit(EStr("key"))))),
            SType(NormalT),
          ),
        ),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)).contains("get key() { throw 0; }"))
    }

    // --- multi-param ---
    check("multi-param: x == 0, y ∈ Object") {
      val goal = List(
        FEq(Sym(Arg(0)), Lit(EMath(0))),
        FEq(TypeOf(Sym(Arg(1))), SType(ObjectT)),
      )
      val result = Solver.solve(goal, List(Arg(0), Arg(1)))
      assert(result.isDefined)
      assert(result.get(Arg(0)) == "0")
      assert(result.get(Arg(1)) == "{}")
    }

    // --- normal completion stripping ---
    check("normal completion on internal method is default — stripped") {
      val goal = List(
        FEq(TypeOf(Sym(Arg(0))), SType(ObjectT)),
        FEq(
          TypeOf(App("Get", List(Sym(Arg(0)), Lit(EStr("a"))))),
          SType(NormalT),
        ),
      )
      val result = Solver.solve(goal, List(Arg(0)))
      assert(result.isDefined)
      assert(result.get(Arg(0)) == "{}")
    }
  }

  init
}
