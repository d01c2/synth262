package synth262.interpreter

import synth262.Synth262Test
import synth262.cfgBuilder.*
import synth262.ir.*
import synth262.state.*

/** test for IR interpreter with a CFG */
trait InterpreterTest extends Synth262Test {
  def category: String = "interpreter"
}
object InterpreterTest {
  // handle interpreter test
  def interp(st: State): State = Interpreter(st)
  def interpFile(filename: String): State =
    interp(State(CFGBuilder(Program.fromFile(filename))))
}
