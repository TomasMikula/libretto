package libretto.testing

import libretto.{CoreBridge, CoreDSL}
import libretto.util.Monad

trait TestDsl {
  val dsl: CoreDSL

  type F[_]

  given F: Monad[F]

  val probes: CoreBridge.Of[dsl.type, F]

  type TestResult

  import dsl.{-⚬, Done}
  import probes.OutPort

  type TestCase = Done -⚬ TestResult

  def success: Done -⚬ TestResult
  def failure: Done -⚬ TestResult

  def extractTestResult(outPort: OutPort[TestResult]): F[libretto.testing.TestResult]
}

object TestDsl {
  transparent inline def givenInstance(using testDsl: TestDsl): testDsl.type =
    testDsl

  transparent inline def dsl(using testDsl: TestDsl): testDsl.dsl.type =
    testDsl.dsl

  def success(using testDsl: TestDsl): testDsl.dsl.-⚬[testDsl.dsl.Done, testDsl.TestResult] =
    testDsl.success
}
