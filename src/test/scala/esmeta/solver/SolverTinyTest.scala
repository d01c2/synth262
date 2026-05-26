package esmeta.solver

import esmeta.ir.*
import Formula.*, SymExpr.*

/** basic solver test */
class SolverTinyTest extends SolverTest {
  val name: String = "solverTinyTest"

  def init: Unit = {
    import SolverTest.*

    checkUnsat("contradiction: x == 0 and x == 1")(
      List(isValue(xSym, EMath(0)), isValue(xSym, EMath(1))),
    )

    checkUnsat("contradiction: x == x and NOT(x == x)")(
      List(FEq(xSym, xSym), FNot(FEq(xSym, xSym))),
    )
  }

  init
}
