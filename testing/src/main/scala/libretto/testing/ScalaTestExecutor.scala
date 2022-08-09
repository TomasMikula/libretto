package libretto.testing

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.{CoreLib, ExecutionParams, Monad, ScalaBridge, ScalaExecutor, ScalaDSL, StarterKit}
import libretto.scalasource.{Position => SourcePos}
import libretto.util.Async
import libretto.testing.ScalaTestExecutor.ExecutionParam.Instantiation

object ScalaTestExecutor {

  class ScalaTestKitFromBridge[DSL <: ScalaDSL, Bridge <: ScalaBridge.Of[DSL]](
    val dsl0: DSL,
    val bridge: Bridge & ScalaBridge.Of[dsl0.type],
  ) extends ScalaTestKit {
      override val dsl: bridge.dsl.type = bridge.dsl
      override val probes: bridge.type = bridge
      import dsl._
      import probes.Execution

      override type Assertion[A] = Val[String] |+| A

      override type ExecutionParam[A] = ScalaTestExecutor.ExecutionParam[A]
      override val ExecutionParam: ManualClockParams[ExecutionParam] =
        ScalaTestExecutor.ExecutionParam.manualClockParamsInstance

      private val coreLib = CoreLib(this.dsl)
      import coreLib.{Monad => _, _}

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
        import TestResult.{Crash, Success, Failure}
        Outcome.asyncTestResult(
          exn.OutPort
            .awaitEither[Val[String], Done](outPort)
            .flatMap {
              case Left(e) =>
                Async.now(Crash(e))
              case Right(Left(msg)) =>
                exn.OutPort.awaitVal(msg).map {
                  case Left(e)    => Crash(e)
                  case Right(msg) => Failure(msg, pos)
                }
              case Right(Right(d)) =>
                exn.OutPort.awaitDone(d).map {
                  case Left(e)   => Crash(e)
                  case Right(()) => Success(())
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
    exec: ScalaExecutor,
  ): TestExecutor[ScalaTestKit] = {
    val kit = ScalaTestKitFromBridge[exec.dsl.type, exec.bridge.type](exec.dsl, exec.bridge)
    fromKitAndExecutor(kit, exec.narrow)
  }

  def fromKitAndExecutor(
    kit: ScalaTestKit { type ExecutionParam[A] = ScalaTestExecutor.ExecutionParam[A] },
    exec: ScalaExecutor.Of[kit.dsl.type, kit.probes.type],
  ): TestExecutor[kit.type] =
    new TestExecutor[kit.type] {
      override val name: String =
        ScalaTestExecutor.getClass.getCanonicalName

      override val testKit: kit.type = kit

      import testKit.{ExecutionParam, Outcome}
      import testKit.dsl._
      import testKit.probes.Execution

      override def runTestCase[O, P, Y](
        body: Done -⚬ O,
        params: ExecutionParam[P],
        conduct: (exn: Execution) ?=> (exn.OutPort[O], P) => Outcome[Y],
        postStop: Y => Outcome[Unit],
      ): TestResult[Unit] = {
        val p: Instantiation[P, exec.ExecutionParam] =
          ScalaTestExecutor.ExecutionParam.instantiate(params)(using exec.ExecutionParam)

        TestExecutor
          .usingExecutor(exec)
          .runTestCase[O, p.X, Y](
            body,
            p.px,
            (port, x) => Outcome.toAsyncTestResult(conduct(port, p.get(x))),
            postStop andThen Outcome.toAsyncTestResult,
          )
      }

      override def runTestCase(body: () => Outcome[Unit]): TestResult[Unit] =
        TestExecutor
          .usingExecutor(exec)
          .runTestCase(() => Outcome.toAsyncTestResult(body()))
    }

  def fromJavaExecutors(
    scheduler: ScheduledExecutorService,
    blockingExecutor: ExecutorService,
  ): TestExecutor[ScalaTestKit] = {
    val executor0: libretto.ScalaExecutor.OfDsl[StarterKit.dsl.type] =
      StarterKit.executor(blockingExecutor)(scheduler)

    fromExecutor(executor0)
  }

  val defaultFactory: TestExecutor.Factory[ScalaTestKit] =
    new TestExecutor.Factory[ScalaTestKit] {
      override val testKit: ScalaTestKitFromBridge[StarterKit.dsl.type, StarterKit.bridge.type] =
        new ScalaTestKitFromBridge(StarterKit.dsl, StarterKit.bridge)

      override def name =
        s"${ScalaTestExecutor.getClass.getSimpleName()} default"

      override type Exec = (ScheduledExecutorService, ExecutorService, TestExecutor[testKit.type])

      override def getExecutor(exec: Exec): TestExecutor[testKit.type] =
        exec._3

      override def create(): Exec = {
        val scheduler = Executors.newScheduledThreadPool(Runtime.getRuntime().availableProcessors())
        val blockingExecutor = Executors.newCachedThreadPool()
        val testExecutor = fromKitAndExecutor(testKit, StarterKit.executor(blockingExecutor)(scheduler))
        (scheduler, blockingExecutor, testExecutor)
      }

      override def shutdown(exec: Exec): Unit = {
        exec._2.shutdownNow()
        exec._1.shutdownNow()
      }
    }

  lazy val global: TestExecutor[ScalaTestKit] =
    defaultFactory.getExecutor(defaultFactory.create())
}
