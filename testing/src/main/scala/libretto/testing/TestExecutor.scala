package libretto.testing

import libretto.{CoreBridge, CoreDSL, CoreExecutor}
import libretto.exec.ExecutionParams
import libretto.exec.Executor.CancellationReason
import libretto.lambda.util.Monad
import libretto.util.Async
import scala.concurrent.duration.FiniteDuration

trait TestExecutor[+TK <: TestKit] { self =>
  val testKit: TK

  import testKit.{ExecutionParams, Outcome}
  import testKit.dsl.*
  import testKit.bridge.Execution

  def name: String

  def execpAndCheck[O, P, X](
    body: Done -⚬ O,
    params: ExecutionParams[P],
    conduct: (exn: Execution) ?=> (exn.OutPort[O], P) => Outcome[X],
    postStopCheck: X => Outcome[Unit],
    timeout: FiniteDuration,
  ): TestResult[Unit]

  def check(
    body: () => Outcome[Unit],
    timeout: FiniteDuration,
  ): TestResult[Unit]

  def execAndCheck[O, X](
    body: Done -⚬ O,
    conduct: (exn: Execution) ?=> exn.OutPort[O] => Outcome[X],
    postStopCheck: X => Outcome[Unit],
    timeout: FiniteDuration,
  ): TestResult[Unit] =
    execpAndCheck[O, Unit, X](body, ExecutionParams.unit, (po, _) => conduct(po), postStopCheck, timeout)

  def exec[O](
    body: Done -⚬ O,
    conduct: (exn: Execution) ?=> exn.OutPort[O] => Outcome[Unit],
    timeout: FiniteDuration,
  ): TestResult[Unit] =
    execAndCheck[O, Unit](body, conduct(_), testKit.Outcome.success, timeout)

  def narrow: TestExecutor[testKit.type] =
    new TestExecutor[testKit.type] {
      export self.{testKit, name, check, execpAndCheck}
    }
}

object TestExecutor {
  trait Factory[+TK <: TestKit] {
    val testKit: TK
    def name: String

    type ExecutorResource

    def create(): ExecutorResource
    def access(r: ExecutorResource): TestExecutor[testKit.type]
    def shutdown(r: ExecutorResource): Unit
  }

  object Factory {
    /** Performs no initialization or shutdown. */
    def noOp[TK <: TestKit](executor: TestExecutor[TK]): Factory[TK] =
      new Factory[TK] {
        override val testKit: executor.testKit.type = executor.testKit
        override def name: String = executor.name
        override type ExecutorResource = TestExecutor[testKit.type]
        override def create(): ExecutorResource = executor.narrow
        override def access(r: ExecutorResource): TestExecutor[testKit.type] = r
        override def shutdown(r: ExecutorResource): Unit = {}
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
        export underlying.{name, check, execpAndCheck, testKit}
      }

      new Factory[TK] {
        override val testKit: kit.type = kit
        override def name: String = factoryName
        override type ExecutorResource = TestExecutorWithShutdown

        override def create(): ExecutorResource = {
          val (executor, shutdown) = acquire()
          new TestExecutorWithShutdown(executor, shutdown)
        }

        override def access(exec: TestExecutorWithShutdown): TestExecutor[testKit.type] =
          exec

        override def shutdown(executor: TestExecutorWithShutdown): Unit =
          executor.shutdown()
      }
    }
  }

  def usingExecutor(executor: CoreExecutor): UsingExecutor[executor.type] =
    new UsingExecutor[executor.type](executor)

  class UsingExecutor[E <: CoreExecutor](val executor: E) {
    import executor.ExecutionParams
    import executor.bridge.Execution
    import executor.dsl.*

    def runTestCase[O, P, X](
      body: Done -⚬ O,
      params: ExecutionParams[P],
      conduct: (exn: Execution) ?=> (exn.OutPort[O], P) => Async[TestResult[X]],
      postStop: X => Async[TestResult[Unit]],
      timeout: FiniteDuration,
    ): TestResult[Unit] = {
      val (executing, p) = executor.execute(body, params)
      import executing.{execution, inPort, outPort}

      val res0: TestResult[X] =
        try {
          execution.InPort.supplyDone(inPort)

          val properResult: Async[TestResult[X]] =
            conduct(using execution)(outPort, p)

          val cancellationResult: Async[TestResult[X]] =
            executor.watchForCancellation(execution).map {
              case CancellationReason.Bug(msg, cause) =>
                TestResult.crash(new RuntimeException(msg, cause.getOrElse(null)))
              case CancellationReason.User(pos) =>
                TestResult.crash(new AssertionError(s"Unexpected call to cancel at ${pos.filename}:${pos.line}"))
            }

          val result: Async[TestResult[X]] =
            Async.race_(properResult, cancellationResult)

          Async
            .await(timeout)(result)
            .getOrElse(TestResult.timedOut(timeout))
        } catch {
          case e => TestResult.crash(e)
        } finally {
          executor.cancel(execution)
        }

      res0.flatMap { x =>
        try {
          Async
            .await(timeout) { postStop(x) }
            .getOrElse(TestResult.timedOut(timeout))
        } catch {
          case e => TestResult.crash(e)
        }
      }
    }

    def runTestCase(
      body: () => Async[TestResult[Unit]],
      timeout: FiniteDuration,
    ): TestResult[Unit] =
      try {
        Async
          .await(timeout)(body())
          .getOrElse(TestResult.timedOut(timeout))
      } catch {
        case e => TestResult.crash(e)
      }
  }
}
