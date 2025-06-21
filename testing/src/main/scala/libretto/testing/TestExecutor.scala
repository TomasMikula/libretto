package libretto.testing

import libretto.exec.{Bridge, ExecutionParams, Executor}
import libretto.exec.Executor.CancellationReason
import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.Indeed
import libretto.util.Async
import scala.concurrent.duration.FiniteDuration

trait TestExecutor[+TK <: TestKit] { self =>
  val testKit: TK

  import testKit.{DefaultInput, ExecutionParams, Outcome}
  import testKit.dsl.*
  import testKit.bridge.Execution

  def name: String

  def execpAndCheck[O, P, X](
    body: DefaultInput -⚬ O,
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
    body: DefaultInput -⚬ O,
    conduct: (exn: Execution) ?=> exn.OutPort[O] => Outcome[X],
    postStopCheck: X => Outcome[Unit],
    timeout: FiniteDuration,
  ): TestResult[Unit] =
    execpAndCheck[O, Unit, X](body, ExecutionParams.unit, (po, _) => conduct(po), postStopCheck, timeout)

  def exec[O](
    body: DefaultInput -⚬ O,
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
  trait Factory[+TK <: libretto.testing.TestKit] {
    type TestKit <: TK
    val testKit: TestKit

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
        override type TestKit = TK
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
        override type TestKit = TK
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

    def from[DSL <: { type -⚬[A, B] }, BRIDGE <: Bridge, TK <: TestKit, P[_]](
      ef: Executor.Factory.Of[DSL, BRIDGE],
      kf: TestKit.Factory[DSL, BRIDGE, TK, P],
      adaptParam: [A] => P[A] => Exists[[X] =>> (ef.ExecutionParam[X], X => A)],
    ): Factory[TK & TestKit.Ofp[ef.dsl.type, ef.bridge.type, P]] =
      new Factory[TK & TestKit.Ofp[ef.dsl.type, ef.bridge.type, P]] {
        override type TestKit =
          TK & TestKit.Ofp[ef.dsl.type, ef.bridge.type, P]

        override val testKit: TestKit =
          kf.create(ef.dsl, ef.bridge)

        override def name: String =
          s"TestExecutor(${ef.name},${kf.name})"

        override type ExecutorResource = (ef.ExecutorResource, TestExecutor[testKit.type])

        override def access(r: ExecutorResource): TestExecutor[testKit.type] =
          r._2

        override def create(): ExecutorResource = {
          val executor = ef.create()
          val exr = ef.access(executor)
          val testExecutor = TestExecutor
            .forKit(testKit)
            .adaptParams[exr.ExecutionParam](adaptParam)
            .usingExecutor(exr)
            .make(name)
          (executor, testExecutor)
        }

        override def shutdown(r: ExecutorResource): Unit =
          ef.shutdown(r._1)
      }
  }

  def forKit(kit: TestKit): ForKit[kit.type, kit.ExecutionParam] =
    ForKit(kit, adaptParam = [A] => pa => Exists((pa, identity)))

  class ForKit[TK <: TestKit, P[_]](
    val kit: TK,
    adaptParam: [A] => kit.ExecutionParam[A] => Exists[[X] =>> (P[X], X => A)],
  ):
    def adaptParams[Q[_]](f: [A] => P[A] => Exists[[X] =>> (Q[X], X => A)]): ForKit[TK, Q] =
      ForKit(
        kit,
        adaptParam = [A] => (ka: kit.ExecutionParam[A]) =>
          adaptParam(ka) match
            case Indeed((py, h)) =>
              f(py) match
                case Indeed((qx, g)) =>
                  Exists((qx, g andThen h))
      )

    def usingExecutor(
      exr: Executor.Of[kit.dsl.type, kit.bridge.type] with { type ExecutionParam[A] = P[A] },
    ): UsingKitAndExecutor[TK, P] =
      UsingKitAndExecutor(kit, adaptParam, exr)

  class UsingKitAndExecutor[TK <: TestKit, P[_]](
    val kit: TK,
    adaptParam: [A] => kit.ExecutionParam[A] => Exists[[X] =>> (P[X], X => A)],
    executor: Executor.Of[kit.dsl.type, kit.bridge.type] with { type ExecutionParam[A] = P[A] },
  ):
    import kit.DefaultInput

    def make(name: String): TestExecutor[TK] =
      val name1 = name
      new TestExecutor[kit.type] {
        override val name: String = name1
        override val testKit: kit.type = kit

        import testKit.{ExecutionParams, Outcome}
        import testKit.dsl.*
        import testKit.bridge.Execution

        override def execpAndCheck[O, P, Y](
          body: DefaultInput -⚬ O,
          params: ExecutionParams[P],
          conduct: (exn: Execution) ?=> (exn.OutPort[O], P) => Outcome[Y],
          postStop: Y => Outcome[Unit],
          timeout: FiniteDuration,
        ): TestResult[Unit] =
          params.adapt(adaptParam) match
            case e @ Indeed((params, adaptResult)) =>
              runOnExecutor[O, e.T, Y](
                  body,
                  params,
                  (port, x) => Outcome.toAsyncTestResult(conduct(port, adaptResult(x))),
                  postStop andThen Outcome.toAsyncTestResult,
                  timeout,
                )

        private def runOnExecutor[O, A, X](
          body: DefaultInput -⚬ O,
          params: executor.ExecutionParams[A],
          conduct: (exn: Execution) ?=> (exn.OutPort[O], A) => Async[TestResult[X]],
          postStop: X => Async[TestResult[Unit]],
          timeout: FiniteDuration,
        ): TestResult[Unit] = {
          val (executing, a) = executor.execute(body, params)
          import executing.{bridge, execution, inPort, outPort}
          given execution.type = execution

          val res0: TestResult[X] =
            try {
              kit.supplyDefaultInput(inPort)

              val properResult: Async[TestResult[X]] =
                conduct(using execution)(outPort, a)

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

        override def check(
          body: () => Outcome[Unit],
          timeout: FiniteDuration,
        ): TestResult[Unit] =
          try {
            Async
              .await(timeout)(Outcome.toAsyncTestResult(body()))
              .getOrElse(TestResult.timedOut(timeout))
          } catch {
            case e => TestResult.crash(e)
          }
      }
}
