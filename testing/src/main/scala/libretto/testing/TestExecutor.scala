package libretto.testing

import libretto.{CoreDSL, Executor}
import libretto.util.Monad
import libretto.util.Monad.syntax._

trait TestExecutor[+TK <: TestKit] {
  val testKit: TK

  import testKit.Outcome
  import testKit.dsl._
  import testKit.probes.OutPort

  def name: String

  def runTestCase[O, X](
    body: Done -⚬ O,
    conduct: OutPort[O] => Outcome[X],
    postStop: X => Outcome[Unit],
  ): TestResult[Unit]

  def runTestCase[O](
    body: Done -⚬ O,
    conduct: OutPort[O] => Outcome[Unit],
  ): TestResult[Unit] =
    runTestCase[O, Unit](body, conduct, testKit.monadOutcome.pure)
}

object TestExecutor {
  def usingExecutor[F[_]](executor: Executor[F]): UsingExecutor[F, executor.type] =
    new UsingExecutor[F, executor.type](executor)

  class UsingExecutor[F[_], E <: Executor[F]](val executor: E) {
    import executor.OutPort
    import executor.dsl._

    def runTestCase[O, X](
      body: Done -⚬ O,
      conduct: OutPort[O] => F[TestResult[X]],
      postStop: X => F[TestResult[Unit]],
    ): TestResult[Unit] = {
      val (outPort, execution) =
        executor.execute(body)

      val res0: TestResult[X] =
        try {
          executor.runAwait {
            conduct(outPort)
          }
        } catch {
          case e => libretto.testing.TestResult.Crash(e)
        } finally {
          executor.cancel(execution)
        }

      res0 match {
        case TestResult.Success(x) =>
          try {
            executor.runAwait {
              postStop(x)
            }
          } catch {
            case e => libretto.testing.TestResult.Crash(e)
          }
        case TestResult.Failure(msg) =>
          TestResult.Failure(msg)
        case TestResult.Crash(e) =>
          TestResult.Crash(e)
      }
    }
  }
}
