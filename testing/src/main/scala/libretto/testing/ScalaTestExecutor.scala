package libretto.testing

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.{CoreLib, Monad, ScalaBridge, ScalaExecutor, ScalaDSL, StarterKit}
import libretto.util.{Monad => ScalaMonad}
import libretto.util.Monad.syntax._
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration._
import scala.util.{Failure, Success, Try}

object ScalaTestExecutor {

  private trait ScalaTestKitFromExecutor[F0[_]: ScalaMonad, DSL <: ScalaDSL, Exec <: ScalaExecutor.Of[DSL, F0]](
    val dsl0: DSL,
    val exec: Exec & ScalaExecutor.Of[dsl0.type, F0],
  ) extends ScalaTestKit {
      override type F[A] = F0[A]
      override val dsl: exec.dsl.type = exec.dsl
      override val probes: exec.type = exec
      import dsl._

      override type Assertion[A] = Val[String] |+| A

      private val coreLib = CoreLib(this.dsl)
      import coreLib.{Monad => _, _}

      override def F: libretto.util.Monad[F0] =
        summon[libretto.util.Monad[F0]]

      override def success[A]: A -⚬ Assertion[A] =
        injectR

      override def failure[A]: Done -⚬ Assertion[A] =
        failure("Failed")

      override def failure[A](msg: String): Done -⚬ Assertion[A] =
        constVal(msg) > injectL

      override def monadAssertion: Monad[-⚬, Assertion] =
        |+|.right[Val[String]]

      override def extractOutcome(outPort: exec.OutPort[Assertion[Done]]): Outcome[Unit] = {
        import TestResult.{Crash, Success, Failure}
        Outcome(
          exec
            .awaitEither[Val[String], Done](outPort)
            .flatMap {
              case Left(e) =>
                F.pure(Crash(e))
              case Right(Left(msg)) =>
                exec.awaitVal(msg).map {
                  case Left(e)    => Crash(e)
                  case Right(msg) => Failure(msg)
                }
              case Right(Right(d)) =>
                exec.awaitDone(d).map {
                  case Left(e)   => Crash(e)
                  case Right(()) => Success(())
                }
            }
        )
      }
  }

  def fromExecutor[F0[_]: ScalaMonad](
    dsl: ScalaDSL,
    exec: ScalaExecutor.Of[dsl.type, F0],
  ): TestExecutor[ScalaTestKit] =
    new TestExecutor[ScalaTestKit] {
      override val name: String =
        ScalaTestExecutor.getClass.getCanonicalName

      override val testKit: ScalaTestKitFromExecutor[F0, dsl.type, exec.type] =
        new ScalaTestKitFromExecutor[F0, dsl.type, exec.type](dsl, exec) {}

      import testKit.Outcome
      import testKit.dsl._
      import testKit.probes.OutPort

      override def runTestCase[O, X](
        body: Done -⚬ O,
        conduct: OutPort[O] => Outcome[X],
        postStop: X => Outcome[Unit],
      ): TestResult[Unit] =
        TestExecutor
          .usingExecutor(exec)
          .runTestCase[O, X](
            body,
            conduct andThen Outcome.unwrap,
            postStop andThen Outcome.unwrap,
          )
    }

  def fromJavaExecutors(
    scheduler: ScheduledExecutorService,
    blockingExecutor: ExecutorService,
  ): TestExecutor[ScalaTestKit] = {
    val executor0: libretto.ScalaExecutor.Of[StarterKit.dsl.type, Future] =
      StarterKit.executor(blockingExecutor)(scheduler)

    given monadFuture: ScalaMonad[Future] =
      ScalaMonad.monadFuture(using ExecutionContext.fromExecutor(scheduler))

    fromExecutor(StarterKit.dsl, executor0)
  }

  lazy val global: TestExecutor[ScalaTestKit] =
    fromJavaExecutors(
      scheduler        = Executors.newScheduledThreadPool(4),
      blockingExecutor = Executors.newCachedThreadPool(),
    )
}
