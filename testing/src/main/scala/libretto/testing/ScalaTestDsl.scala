package libretto.testing

import libretto.ScalaDSL

trait ScalaTestDsl extends TestDsl {
  override val dsl: ScalaDSL

  import dsl.{-⚬, Val}

  def assertEquals[A](expected: A): Val[A] -⚬ TestResult
}
