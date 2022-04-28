package libretto.testing

import libretto.ScalaDSL

trait ScalaTestDsl extends TestDsl {
  override val dsl: ScalaDSL
}
