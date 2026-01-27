package esmeta.injector

import esmeta.ESMetaTest
import esmeta.state.*

/** test for assertion injector */
trait InjectorTest extends ESMetaTest {
  def category: String = "injector"

  lazy val cfg = ESMetaTest.cfg

  lazy val sameValueTest = Injector(cfg, "42;")
  lazy val throwsTest = Injector(cfg, "null.x;")
  lazy val compareArrayTest = Injector(cfg, "[1, 2, 3];")
}
