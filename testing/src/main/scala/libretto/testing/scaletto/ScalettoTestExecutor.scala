package libretto.testing.scaletto

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.{CoreLib, ExecutionParams, Monad}
import libretto.lambda.util.SourcePos
import libretto.scaletto.{Scaletto, ScalettoBridge, ScalettoExecutor, StarterKit}
import libretto.testing.{ManualClock, ManualClockParams, TestExecutor, TestResult}
import libretto.util.Async
import scala.concurrent.duration.FiniteDuration

object ScalettoTestExecutor {
  import ExecutionParam.Instantiation

  class ScalettoTestKitFromBridge[DSL <: Scaletto, Bridge <: ScalettoBridge.Of[DSL]](
    val dsl0: DSL,
    val bridge0: Bridge & ScalettoBridge.Of[dsl0.type],
  ) extends ScalettoTestKit {
      override type Dsl = bridge.dsl.type

      override val dsl: bridge0.dsl.type = bridge0.dsl
      override val bridge: bridge0.type = bridge0
      import dsl.*
      import bridge.Execution

      override type Assertion[A] = Val[String] |+| A

      override type ExecutionParam[A] = ScalettoTestExecutor.ExecutionParam[A]
      override val ExecutionParam: ManualClockParams[ExecutionParam] =
        ScalettoTestExecutor.ExecutionParam.manualClockParamsInstance

      private val coreLib = CoreLib(this.dsl)
      import coreLib.{Monad as _, *}

      override def success[A]: A -⚬ Assertion[A] =
        injectR

      override def failure[A]: Done -⚬ Assertion[A] =
        failure("Failed")

      override def failure[A](msg: String): Done -⚬ Assertion[A] =
        constVal(msg) > injectL

      override def monadAssertion: Monad[-⚬, Assertion] =
        |+|.right[Val[String]]

      override def extractOutcome(using exn: Execution, pos: SourcePos)(
        outPort: exn.OutPort[Assertion[Done]],
      ): Outcome[Unit] = {
        import TestResult.{crash, success as succeed, failed as fail}
        Outcome.asyncTestResult(
          exn.OutPort
            .awaitEither[Val[String], Done](outPort)
            .flatMap {
              case Left(e) =>
                Async.now(crash(e))
              case Right(Left(msg)) =>
                exn.OutPort.awaitVal(msg).map {
                  case Left(e)    => crash(e)
                  case Right(msg) => fail(using pos)(msg)
                }
              case Right(Right(d)) =>
                exn.OutPort.awaitDone(d).map {
                  case Left(e)   => crash(e)
                  case Right(()) => succeed(())
                }
            }
        )
      }
  }

  opaque type ExecutionParam[A] = ExecutionParams.Free[ExecutionParam.F, A]
  object ExecutionParam {
    sealed trait F[A]
    case object ManualClockParam extends F[ManualClock]

    def manualClock: ExecutionParam[ManualClock] =
      ExecutionParams.Free.wrap(ManualClockParam)

    given manualClockParamsInstance: ManualClockParams[ExecutionParam] with {
      override def unit =
        ExecutionParams.Free.unit
      override def pair[A, B](a: ExecutionParam[A], b: ExecutionParam[B]): ExecutionParam[(A, B)] =
        ExecutionParams.Free.pair(a, b)
      override def manualClock: ExecutionParam[ManualClock] =
        ExecutionParams.Free.wrap(ManualClockParam)
    }

    def instantiate[A, P[_]](p: ExecutionParam[A])(using
      ep: ExecutionParams.WithScheduler[P],
    ): Instantiation[A, P] = {
      import ExecutionParams.Free.{Ext, One, Zip}

      p match {
        case _: One[F] =>
          Instantiation[P, Unit, Unit](ep.unit, _ => ())
        case z: Zip[F, a, b] =>
          val (ia, ib) = (instantiate(z.a), instantiate(z.b))
          Instantiation[P, (ia.X, ib.X), A](ep.pair(ia.px, ib.px), { case (x, y) => (ia.get(x), ib.get(y)) })
        case Ext(ManualClockParam) =>
          val (clock, scheduler) = ManualClock.scheduler()
          Instantiation[P, Unit, ManualClock](ep.scheduler(scheduler), _ => clock)
      }
    }

    sealed abstract class Instantiation[A, P[_]] {
      type X

      val px: P[X]
      def get(x: X): A
    }

    object Instantiation {
      def apply[P[_], X0, A](px0: P[X0], f: X0 => A): Instantiation[A, P] =
        new Instantiation[A, P] {
          override type X = X0
          override val px = px0
          override def get(x: X) = f(x)
        }
    }
  }

  def fromExecutor(
    exec: ScalettoExecutor,
  ): TestExecutor[ScalettoTestKit.Of[exec.dsl.type]] = {
    val kit = ScalettoTestKitFromBridge[exec.dsl.type, exec.bridge.type](exec.dsl, exec.bridge)
    fromKitAndExecutor(kit, exec.narrow)
  }

  def fromKitAndExecutor(
    kit: ScalettoTestKit { type ExecutionParam[A] = ScalettoTestExecutor.ExecutionParam[A] },
    exr: ScalettoExecutor.Of[kit.dsl.type, kit.bridge.type],
  ): TestExecutor[kit.type] =
    new TestExecutor[kit.type] {
      override val name: String =
        ScalettoTestExecutor.getClass.getCanonicalName

      override val testKit: kit.type = kit

      import testKit.{ExecutionParam, Outcome}
      import testKit.dsl.*
      import testKit.bridge.Execution

      override def execpAndCheck[O, P, Y](
        body: Done -⚬ O,
        params: ExecutionParam[P],
        conduct: (exn: Execution) ?=> (exn.OutPort[O], P) => Outcome[Y],
        postStop: Y => Outcome[Unit],
        timeout: FiniteDuration,
      ): TestResult[Unit] = {
        val p: Instantiation[P, exr.ExecutionParam] =
          ScalettoTestExecutor.ExecutionParam.instantiate(params)(using exr.ExecutionParam)

        TestExecutor
          .usingExecutor(exr)
          .runTestCase[O, p.X, Y](
            body,
            p.px,
            (port, x) => Outcome.toAsyncTestResult(conduct(port, p.get(x))),
            postStop andThen Outcome.toAsyncTestResult,
            timeout,
          )
      }

      override def check(
        body: () => Outcome[Unit],
        timeout: FiniteDuration,
      ): TestResult[Unit] =
        TestExecutor
          .usingExecutor(exr)
          .runTestCase(() => Outcome.toAsyncTestResult(body()), timeout)
    }

  def fromJavaExecutors(
    scheduler: ScheduledExecutorService,
    blockingExecutor: ExecutorService,
  ): TestExecutor[ScalettoTestKit] = {
    val executor0: ScalettoExecutor.OfDsl[StarterKit.dsl.type] =
      StarterKit.executor(blockingExecutor)(scheduler)

    fromExecutor(executor0)
  }

  def defaultFactory(
    ef: ScalettoExecutor.Factory,
  ): TestExecutor.Factory[ScalettoTestKit.Of[ef.dsl.type]] =
    new TestExecutor.Factory[ScalettoTestKit.Of[ef.dsl.type]] {
      override val testKit: ScalettoTestKitFromBridge[ef.dsl.type, ef.bridge.type] =
        new ScalettoTestKitFromBridge(ef.dsl, ef.bridge)

      override def name: String =
        s"ScalettoTestExecutor.defaultFactory(${ef.name})"

      override type ExecutorResource = (ef.ExecutorResource, TestExecutor[testKit.type])

      override def access(r: ExecutorResource): TestExecutor[testKit.type] =
        r._2

      override def create(): ExecutorResource = {
        val executor = ef.create()
        val testExecutor = fromKitAndExecutor(testKit, ef.access(executor))
        (executor, testExecutor)
      }

      override def shutdown(r: ExecutorResource): Unit =
        ef.shutdown(r._1)
    }

  val defaultFactory: TestExecutor.Factory[ScalettoTestKit] =
    defaultFactory(ScalettoExecutor.defaultFactory)

  lazy val global: TestExecutor[ScalettoTestKit] =
    defaultFactory.access(defaultFactory.create())
}
