package libretto.testing

import libretto.{CoreDSL, Executor}
import libretto.util.{Async, Monad}
import libretto.util.Monad.syntax._

trait TestExecutor[TK <: TestKit] { self =>
  val testKit: TK

  import testKit.{ExecutionParam, Outcome}
  import testKit.dsl._
  import testKit.probes.Execution

  def name: String

  def runTestCase[O, P, X](
    body: Done -⚬ O,
    params: ExecutionParam[P],
    conduct: (exn: Execution) ?=> (exn.OutPort[O], P) => Outcome[X],
    postStop: X => Outcome[Unit],
  ): TestResult[Unit]

  def runTestCase(body: () => Outcome[Unit]): TestResult[Unit]

  def runTestCase[O, X](
    body: Done -⚬ O,
    conduct: (exn: Execution) ?=> exn.OutPort[O] => Outcome[X],
    postStop: X => Outcome[Unit],
  ): TestResult[Unit] =
    runTestCase[O, Unit, X](body, ExecutionParam.unit, (po, _) => conduct(po), postStop)

  def runTestCase[O](
    body: Done -⚬ O,
    conduct: (exn: Execution) ?=> exn.OutPort[O] => Outcome[Unit],
  ): TestResult[Unit] =
    runTestCase[O, Unit](body, conduct(_), testKit.monadOutcome.pure)

  def narrow: TestExecutor[testKit.type] =
    new TestExecutor[testKit.type] {
      export self.{testKit, name, runTestCase}
    }
}

object TestExecutor {
  trait Factory[TK <: TestKit] {
    val testKit: TK
    def name: String

    type Exec <: TestExecutor[testKit.type]

    def create(): Exec
    def shutdown(executor: Exec): Unit
  }

  object Factory {
    /** Performs no initialization or shutdown. */
    def noOp[TK <: TestKit](executor: TestExecutor[TK]): Factory[TK] =
      new Factory[TK] {
        override val testKit: executor.testKit.type = executor.testKit
        override def name: String = executor.name
        override type Exec = TestExecutor[testKit.type]
        override def create(): Exec = executor.narrow
        override def shutdown(exec: Exec): Unit = {}
      }

    def fromAcquire[TK <: TestKit](
      factoryName: String,
      kit: TK,
      acquire: () => (TestExecutor[kit.type], () => Unit),
    ): Factory[TK] = {
      class TestExecutorWithShutdown(
        val underlying: TestExecutor[kit.type],
        val shutdown: () => Unit,
      ) extends TestExecutor[kit.type] {
        export underlying.{name, runTestCase, testKit}
      }

      new Factory[TK] {
        override val testKit: kit.type = kit
        override def name: String = factoryName
        override type Exec = TestExecutorWithShutdown

        override def create(): Exec = {
          val (executor, shutdown) = acquire()
          new TestExecutorWithShutdown(executor, shutdown)
        }

        override def shutdown(executor: TestExecutorWithShutdown): Unit =
          executor.shutdown()
      }
    }
  }

  def usingExecutor(executor: Executor): UsingExecutor[executor.type] =
    new UsingExecutor[executor.type](executor)

  class UsingExecutor[E <: Executor](val executor: E) {
    import executor.ExecutionParam
    import executor.bridge.Execution
    import executor.dsl._

    def runTestCase[O, P, X](
      body: Done -⚬ O,
      params: ExecutionParam[P],
      conduct: (exn: Execution) ?=> (exn.OutPort[O], P) => Async[TestResult[X]],
      postStop: X => Async[TestResult[Unit]],
    ): TestResult[Unit] = {
      val (executing, p) = executor.execute(body, params)
      import executing.{execution, inPort, outPort}

      val res0: TestResult[X] =
        try {
          execution.InPort.supplyDone(inPort)
          Async.await {
            conduct(using execution)(outPort, p)
          }
        } catch {
          case e => TestResult.Crash(e)
        } finally {
          executor.cancel(execution)
        }

      res0 match {
        case TestResult.Success(x) =>
          try {
            Async.await {
              postStop(x)
            }
          } catch {
            case e => TestResult.Crash(e)
          }
        case TestResult.Failure(msg, pos) =>
          TestResult.Failure(msg, pos)
        case TestResult.Crash(e) =>
          TestResult.Crash(e)
      }
    }

    def runTestCase(body: () => Async[TestResult[Unit]]): TestResult[Unit] =
      try {
        Async.await(body())
      } catch {
        case e => TestResult.crash(e)
      }
  }
}
