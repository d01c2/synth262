package synth262.injector

import synth262.Synth262Test
import synth262.cfg.*
import synth262.error.*
import synth262.ir.{Func => IRFunc, FuncKind => IRFuncKind, *}
import synth262.state.*
import synth262.ty.*
import scala.collection.mutable.ListBuffer

/** test for assertion injector */
trait InjectorTest extends Synth262Test {
  def category: String = "injector"

  // assertions
  lazy val hasValue = HasValue("x.y.z", Null)
  lazy val isExtensible = IsExtensible(addr, "x.y.z", true)
  lazy val isNotExtensible = IsExtensible(addr, "x.y.z", false)
  lazy val isCallable = IsCallable(addr, "x.y.z", true)
  lazy val isNotCallable = IsCallable(addr, "x.y.z", false)
  lazy val isConstructable = IsConstructable(addr, "x.y.z", true)
  lazy val isNotConstructable = IsConstructable(addr, "x.y.z", false)
  lazy val compareArray = CompareArray(addr, "x.y.z", List(1, 2, 3))
  lazy val sameObject = SameObject(addr, "x.y.z", "a.b.c")
  lazy val verifyProperty = VerifyProperty(addr, "x.y.z", "p", Map("a" -> Null))

  // exit tags
  import ExitTag.*
  lazy val normal = Normal
  lazy val timeout = Timeout
  lazy val specError = SpecError(InvalidNodeId(42), ExitCursor(func))
  lazy val throwValue = ThrowValue(Vector(Null))

  // conformance tests
  lazy val conformTest = ConformTest(
    id = 42,
    script = "var x = 42;",
    exitTag = normal,
    async = false,
    assertions = Vector(hasValue, isCallable),
  )

  lazy val addr = DynamicAddr(42)
  lazy val irMainFunc =
    IRFunc(true, IRFuncKind.AbsOp, "f", Nil, Type(NumberT), ISeq(Nil))
  lazy val func = Func(0, irMainFunc, Block(0, ListBuffer.empty))
}
