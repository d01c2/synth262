package esmeta.solver

import esmeta.ESMetaTest
import esmeta.ir.*
import esmeta.ty.*
import Formula.*, Term.*

class SolverTest extends ESMetaTest {
  val name = "solverTest"
  val category = "solver"

  def init: Unit = {
    // --- literal equality ---
    check("literal equality: x == 0") {
      val goal = List(FEq(TVar("x"), TLit(EMath(0))))
      val result = Solver.solve(goal, List("x"))
      assert(result == Some(Map("x" -> "0")))
    }

    check("literal equality: x == NaN") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(NumberT)),
        FEq(TVar("x"), TLit(ENumber(Double.NaN))),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.get("x") == "NaN")
    }

    check("literal equality: x == \"hello\"") {
      val goal = List(FEq(TVar("x"), TLit(EStr("hello"))))
      val result = Solver.solve(goal, List("x"))
      assert(result == Some(Map("x" -> "\"hello\"")))
    }

    // --- type narrowing ---
    check("type narrowing: x ∈ Object") {
      val goal = List(FEq(TTypeOf(TVar("x")), TType(ObjectT)))
      val result = Solver.solve(goal, List("x"))
      assert(result.get("x") == "{}")
    }

    check("type narrowing: x ∈ String") {
      val goal = List(FEq(TTypeOf(TVar("x")), TType(StrT)))
      val result = Solver.solve(goal, List("x"))
      assert(result.get("x") == "\"\"")
    }

    check("type narrowing: x ∈ Function") {
      val goal = List(FEq(TTypeOf(TVar("x")), TType(FunctionT)))
      val result = Solver.solve(goal, List("x"))
      assert(result.get("x") == "() => {}")
    }

    // --- type exclusion ---
    check("type exclusion: x ∉ Object") {
      val goal = List(FNot(FEq(TTypeOf(TVar("x")), TType(ObjectT))))
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x") != "{}")
    }

    // --- inequality ---
    check("inequality: x != null") {
      val goal = List(FNot(FEq(TVar("x"), TLit(ENull()))))
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x") != "null")
    }

    check("inequality: x != undefined") {
      val goal = List(FNot(FEq(TVar("x"), TLit(EUndef()))))
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x") != "undefined")
    }

    // --- property constraints ---
    check("property: Get(x, \"name\") == \"foo\"") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(ObjectT)),
        FEq(
          TApp("Get", List(TVar("x"), TLit(EStr("name")))),
          TLit(EStr("foo")),
        ),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x").contains("name: \"foo\""))
    }

    check("property: Get(x, \"value\") ∈ Abrupt") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(ObjectT)),
        FEq(
          TTypeOf(TApp("Get", List(TVar("x"), TLit(EStr("value"))))),
          TType(AbruptT),
        ),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x").contains("get value() { throw 0; }"))
    }

    check("property: HasProperty(x, \"foo\") == true") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(ObjectT)),
        FEq(
          TApp("HasProperty", List(TVar("x"), TLit(EStr("foo")))),
          TLit(EBool(true)),
        ),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x").contains("foo"))
    }

    // --- object config ---
    check("config: IsExtensible(x) == false") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(ObjectT)),
        FEq(TApp("IsExtensible", List(TVar("x"))), TLit(EBool(false))),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x").contains("Object.preventExtensions"))
    }

    check("config: GetPrototypeOf(x) == null") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(ObjectT)),
        FEq(TApp("GetPrototypeOf", List(TVar("x"))), TLit(ENull())),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x").contains("Object.create(null)"))
    }

    // --- proxy ---
    check("proxy: PreventExtensions(x) == false") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(ObjectT)),
        FEq(
          TApp("PreventExtensions", List(TVar("x"))),
          TLit(EBool(false)),
        ),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x").contains("new Proxy"))
    }

    check("proxy: Call(x) ∈ Abrupt") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(FunctionT)),
        FEq(TTypeOf(TApp("Call", List(TVar("x")))), TType(AbruptT)),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x").contains("new Proxy"))
    }

    // --- composition ---
    check("composed: Get normal + Get abrupt on same object") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(ObjectT)),
        FEq(
          TApp("Get", List(TVar("x"), TLit(EStr("name")))),
          TLit(EUndef()),
        ),
        FEq(
          TTypeOf(TApp("Get", List(TVar("x"), TLit(EStr("message"))))),
          TType(AbruptT),
        ),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      val js = result.get("x")
      assert(js.contains("name: undefined"))
      assert(js.contains("get message() { throw 0; }"))
    }

    // --- variable elimination ---
    check("eliminate: y == x, y ∈ Object → x == {}") {
      val goal = List(
        FEq(TVar("y"), TVar("x")),
        FEq(TTypeOf(TVar("y")), TType(ObjectT)),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x") == "{}")
    }

    // --- contradiction ---
    check("contradiction: x == 0 ∧ x == 1 → None") {
      val goal = List(
        FEq(TVar("x"), TLit(EMath(0))),
        FEq(TVar("x"), TLit(EMath(1))),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isEmpty)
    }

    check("contradiction: x == x ∧ NOT(x == x) → None") {
      val goal = List(
        FEq(TVar("x"), TVar("x")),
        FNot(FEq(TVar("x"), TVar("x"))),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isEmpty)
    }

    // --- completion normalization ---
    check("completion: NOT(Normal) normalized to Abrupt") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(ObjectT)),
        FNot(
          FEq(
            TTypeOf(TApp("Get", List(TVar("x"), TLit(EStr("key"))))),
            TType(NormalT),
          ),
        ),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      assert(result.get("x").contains("get key() { throw 0; }"))
    }

    // --- multi-param ---
    check("multi-param: x == 0, y ∈ Object") {
      val goal = List(
        FEq(TVar("x"), TLit(EMath(0))),
        FEq(TTypeOf(TVar("y")), TType(ObjectT)),
      )
      val result = Solver.solve(goal, List("x", "y"))
      assert(result.isDefined)
      assert(result.get("x") == "0")
      assert(result.get("y") == "{}")
    }

    // --- normal completion stripping ---
    check("normal completion on internal method is default — stripped") {
      val goal = List(
        FEq(TTypeOf(TVar("x")), TType(ObjectT)),
        FEq(
          TTypeOf(TApp("Get", List(TVar("x"), TLit(EStr("a"))))),
          TType(NormalT),
        ),
      )
      val result = Solver.solve(goal, List("x"))
      assert(result.isDefined)
      // normal Get is default behavior, so just an object suffices
      assert(result.get("x") == "{}")
    }
  }

  init
}
