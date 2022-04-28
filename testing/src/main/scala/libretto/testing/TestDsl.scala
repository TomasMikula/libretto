package libretto.testing

import libretto.CoreDSL

trait TestDsl {
  val dsl: CoreDSL

  type TestResult

  import dsl.{-⚬, Done}

  type TestCase = Done -⚬ TestResult

  def success: Done -⚬ TestResult
  def failure: Done -⚬ TestResult
}

object TestDsl {
  transparent inline def apply()(using testDsl: TestDsl): testDsl.type =
    testDsl

  transparent inline def dsl(using testDsl: TestDsl): testDsl.dsl.type =
    testDsl.dsl

  def success(using testDsl: TestDsl): testDsl.dsl.-⚬[testDsl.dsl.Done, testDsl.TestResult] =
    testDsl.success
}
