package libretto.testing.core

import libretto.core.{CoreDSL, CoreBridge}
import libretto.lambda.util.SourcePos
import libretto.testing.{TestKit, TestResult}
import scala.concurrent.duration.FiniteDuration

trait CoreTestKit extends TestKit {
  override type Dsl <: CoreDSL

  override val bridge: CoreBridge.Of[dsl.type]

  import dsl.{-⚬, |*|, |+|, Done, Ping}
  import bridge.*

  override type DefaultInput = Done

  override def supplyDefaultInput(using exn: Execution)(port: exn.InPort[Done]): Unit =
    port.supplyDone()

  extension (using exn: Execution, pos: SourcePos)(port: exn.OutPort[Done]) {
    def expectDone: Outcome[Unit] =
      Outcome.asyncTestResult(
        port.awaitDone().map {
          case Left(e)   => TestResult.crash(e)
          case Right(()) => TestResult.success(())
        }
      )

    def expectCrashDone: Outcome[Throwable] =
      Outcome.asyncTestResult(
        port.awaitDone().map {
          case Left(e)   => TestResult.success(e)
          case Right(()) => TestResult.failed(using pos)("Expected crash, but got Done")
        }
      )
  }

  extension (using exn: Execution, pos: SourcePos)(port: exn.OutPort[Ping]) {
    def expectPing: Outcome[Unit] =
      Outcome.asyncTestResult(
        port.awaitPing().map {
          case Left(e)   => TestResult.crash(e)
          case Right(()) => TestResult.success(())
        }
      )

    def expectNoPingFor(duration: FiniteDuration): Outcome[exn.OutPort[Ping]] =
      Outcome.asyncTestResult(
        port.awaitNoPing(duration).map {
          case Left(Left(e))   => TestResult.crash(e)
          case Left(Right(())) => TestResult.failed(using pos)(s"Expected no Ping for $duration, but got Ping")
          case Right(port)     => TestResult.success(port)
        }
      )

    def expectNoPingThenIgnore(duration: FiniteDuration): Outcome[Unit] =
      Outcome.map(
        port.expectNoPingFor(duration)
      ) { port =>
        port
          .append(dsl.dismissPing)
          .discardOne()
      }
  }

  extension [A, B](using exn: Execution, pos: SourcePos)(port: exn.OutPort[A |+| B]) {
    def expectLeft: Outcome[exn.OutPort[A]] =
      Outcome.asyncTestResult(
        port.awaitEither().map {
          case Left(e)         => TestResult.crash(e)
          case Right(Left(p))  => TestResult.success(p)
          case Right(Right(_)) => TestResult.failed(using pos)("Expected Left, but got Right")
        }
      )

    def expectRight: Outcome[exn.OutPort[B]] =
      Outcome.asyncTestResult(
        port.awaitEither().map {
          case Left(e)         => TestResult.crash(e)
          case Right(Left(_))  => TestResult.failed(using pos)("Expected Right, but got Left")
          case Right(Right(p)) => TestResult.success(p)
        }
      )
  }

}
