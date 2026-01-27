package esmeta.injector

import esmeta.ESMetaTest
import esmeta.state.*

/** test for assertion injector */
trait InjectorTest extends ESMetaTest {
  def category: String = "injector"

  lazy val cfg = ESMetaTest.cfg

  lazy val normalExitTest = Injector(cfg, "42;")
  lazy val throwExitTest = Injector(cfg, "null.foo;")
}
