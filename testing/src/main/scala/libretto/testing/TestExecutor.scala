package libretto.testing

import libretto.{CoreDSL, Executor}
import libretto.util.Monad
import libretto.util.Monad.syntax._

trait TestExecutor[+TDSL <: TestDsl] {
  val testDsl: TDSL

  import testDsl.Outcome
  import testDsl.dsl._
  import testDsl.probes.OutPort

  def name: String

  def runTestCase[O](
    body: Done -⚬ O,
    conduct: OutPort[O] => Outcome[Unit],
  ): TestResult[Unit]
}

object TestExecutor {
  def usingExecutor[F[_]](executor: Executor[F]): UsingExecutor[F, executor.type] =
    new UsingExecutor[F, executor.type](executor)

  class UsingExecutor[F[_], E <: Executor[F]](val executor: E) {
    import executor.OutPort
    import executor.dsl._

    def runTestCase[O](
      body: Done -⚬ O,
      conduct: OutPort[O] => F[TestResult[Unit]],
    ): TestResult[Unit] = {
      val (outPort, execution) = executor.execute(body)
      try {
        executor.runAwait {
          conduct(outPort)
        }
      } catch {
        case e => libretto.testing.TestResult.Crash(e)
      } finally {
        executor.cancel(execution)
      }
    }
  }
}
