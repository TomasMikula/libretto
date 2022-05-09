package libretto.testing

import libretto.Executor
import libretto.util.Monad
import libretto.util.Monad.syntax._

trait TestExecutor[TDSL <: TestDsl] {
  val testDsl: TDSL

  import testDsl.dsl._

  def runTestCase(testCase: Done -⚬ testDsl.TestResult): TestResult
}

trait TestExecutorFromExecutor[TDSL <: TestDsl] extends TestExecutor[TDSL] {
  type F[_]

  val executor: Executor[testDsl.dsl.type, F]

  given F: Monad[F]

  import testDsl.dsl._
  import executor._

  def extractTestResult(resultPort: OutPort[testDsl.TestResult]): F[TestResult]

  override def runTestCase(testCase: Done -⚬ testDsl.TestResult): TestResult = {
    val (inPort, outPort, execution) = executor.execute(testCase)
    try {
      executor.runAwait {
        for {
          _   <- executor.signalDone(inPort)
          res <- extractTestResult(outPort)
        } yield res
      }
    } catch {
      case e => TestResult.Crash(e)
    } finally {
      executor.cancel(execution)
    }
  }
}
