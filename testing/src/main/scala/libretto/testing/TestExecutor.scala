package libretto.testing

import libretto.{CoreDSL, Executor}
import libretto.util.Monad
import libretto.util.Monad.syntax._

trait TestExecutor[+TK <: TestKit] {
  val testKit: TK

  import testKit.Outcome
  import testKit.dsl._
  import testKit.probes.Execution

  def name: String

  def runTestCase[O, X](
    body: Done -⚬ O,
    conduct: (exn: Execution) ?=> exn.OutPort[O] => Outcome[X],
    postStop: X => Outcome[Unit],
  ): TestResult[Unit]

  def runTestCase[O](
    body: Done -⚬ O,
    conduct: (exn: Execution) ?=> exn.OutPort[O] => Outcome[Unit],
  ): TestResult[Unit] =
    runTestCase[O, Unit](body, conduct(_), testKit.monadOutcome.pure)
}

object TestExecutor {
  def usingExecutor[F[_]: Monad](executor: Executor[F]): UsingExecutor[F, executor.type] =
    new UsingExecutor[F, executor.type](executor)

  class UsingExecutor[F[_]: Monad, E <: Executor[F]](val executor: E) {
    import executor.Execution
    import executor.dsl._

    def runTestCase[O, X](
      body: Done -⚬ O,
      conduct: (exn: Execution) ?=> exn.OutPort[O] => F[TestResult[X]],
      postStop: X => F[TestResult[Unit]],
    ): TestResult[Unit] = {
      val executing = executor.execute(body)
      import executing.{execution, inPort, outPort}

      val res0: TestResult[X] =
        try {
          executor.runAwait {
            for {
              _   <- execution.InPort.supplyDone(inPort)
              res <- conduct(using execution)(outPort)
            } yield res
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
