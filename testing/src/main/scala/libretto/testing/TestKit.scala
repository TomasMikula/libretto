package libretto.testing

import libretto.cats.Monad
import libretto.core.{CoreBridge, CoreDSL}
import libretto.exec.ExecutionParams
import libretto.lambda.util.{Monad as ScalaMonad, SourcePos}
import libretto.util.Async
import scala.annotation.targetName
import scala.concurrent.duration.FiniteDuration

trait TestKit {
  type Dsl <: CoreDSL

  val dsl: Dsl

  opaque type Outcome[A] = Async[TestResult[A]]
  object Outcome {
    def asyncTestResult[A](fa: Async[TestResult[A]]): Outcome[A] =
      fa

    def toAsyncTestResult[A](outcome: Outcome[A]): Async[TestResult[A]] =
      outcome

    def fromTestResult[A](res: TestResult[A]): Outcome[A] =
      Async.now(res)

    def success[A](a: A): Outcome[A] =
      fromTestResult(TestResult.success(a))

    def assertThrows[A](using pos: SourcePos)(a: => A): Outcome[Throwable] =
      try {
        a
        failure(using pos)("Expected exception, nothing was thrown")
      } catch {
        case e => success(e)
      }

    def assertThrows[A, B](using pos: SourcePos)(a: => A)(recover: PartialFunction[Throwable, B]): Outcome[B] =
      monadOutcome.flatMap(assertThrows(using pos)(a)) {
        case recover(b) => success(b)
        case e          => crash(e)
      }

    def assertNotThrows[A](using pos: SourcePos)(a: => A): Outcome[Unit] =
      try {
        a
        success(())
      } catch {
        case e => failure(using pos)(s"Failed with exception: $e", Some(e))
      }

    def failure[A](using pos: SourcePos)(
      msg: String,
      error: Option[Throwable] = None,
    ): Outcome[A] =
      fromTestResult(TestResult.failed(using pos)(msg, error))

    def crash[A](e: Throwable): Outcome[A] =
      fromTestResult(TestResult.crash(e))

    def assert(using pos: SourcePos)(condition: Boolean, failMsg: String = "Assertion failed"): Outcome[Unit] =
      if (condition)
        success(())
      else
        failure(using pos)(failMsg)

    /** Alias for [[assert]]. */
    def assertTrue(using pos: SourcePos)(condition: Boolean): Outcome[Unit] =
      assert(using pos)(condition)

    /** Alias for [[assert]]. */
    def assertTrue(using pos: SourcePos)(condition: Boolean, failMsg: String): Outcome[Unit] =
      assert(using pos)(condition, failMsg)

    def assertEquals[A](actual: A, expected: A)(using pos: SourcePos): Outcome[Unit] =
      assert(using pos)(
        actual == expected,
        failMsg = s"$actual did not equal $expected",
      )

    def assertLeft[A, B](using pos: SourcePos)(value: Either[A, B]): Outcome[A] =
      value match
        case Left(a) => success(a)
        case other   => failure(using pos)(s"Expected Left, got $other")

    def assertRight[A, B](using pos: SourcePos)(value: Either[A, B]): Outcome[B] =
      value match
        case Right(b) => success(b)
        case other    => failure(using pos)(s"Expected Right, got $other")

    def assertMatches[A, B](using pos: SourcePos)(value: A)(f: PartialFunction[A, B]): Outcome[B] =
      if (f.isDefinedAt(value))
        success(f(value))
      else
        failure(using pos)(s"$value did not match the pattern")

    def assertSubstring(using pos: SourcePos)(substr: String, str: String): Outcome[Unit] =
      assert(using pos)(
        str.contains(substr),
        s"'$str' did not contain '$substr'",
      )

    def traverseIterator[A, B](it: Iterator[A])(f: A => Outcome[B]): Outcome[List[B]] =
      if (it.hasNext) {
        monadOutcome.flatMap(f(it.next()))(b => monadOutcome.map(traverseIterator(it)(f))(b :: _))
      } else {
        success(Nil)
      }

    def traverse[A, B](as: Iterable[A])(f: A => Outcome[B]): Outcome[List[B]] =
      traverseIterator(as.iterator)(f)

    def traverseList[A, B](as: List[A])(f: A => Outcome[B]): Outcome[List[B]] =
      as match {
        case Nil => success(Nil)
        case h :: t => monadOutcome.flatMap(f(h))(b => monadOutcome.map(traverseList(t)(f))(b :: _))
      }

    def zipWith[A, B, C](a: Outcome[A], b: Outcome[B])(f: (A, B) => C): Outcome[C] =
      Async.zipWith(a, b) { (a, b) => (a zipWith b)(f) }

    def assertAll(outcomes: Outcome[Unit]*): Outcome[Unit] =
      outcomes.foldRight(Outcome.success(()))(zipWith(_, _)((_, _) => ()))

    extension [A](outcome: Outcome[A]) {
      def withFilter(f: A => Boolean)(using pos: SourcePos): Outcome[A] =
        Outcome.flatMap(outcome) { a =>
          if (f(a)) Outcome.success(a)
          else      Outcome.failure(using pos)(s"$a did not pass the filter")
        }

      def map[B](f: A => B): Outcome[B] =
        outcome.map(_.map(f))

      def flatMap[B](f: A => Outcome[B]): Outcome[B] =
        outcome.flatMap {
          case TestResult.Success(a)   => f(a)
          case TestResult.Failures(es) => Async.now(TestResult.Failures(es))
        }
    }

    // not given to avoid clash of Monad's extension methods `map`, `flatMap`
    // with the same extension methods directly on Outcome
    val monadOutcome: ScalaMonad[Outcome] =
      new ScalaMonad[Outcome] {
        override def pure[A](a: A): Outcome[A] =
          success(a)

        extension [A](fa: Outcome[A])
          override def flatMap[B](f: A => Outcome[B]): Outcome[B] =
            Outcome.flatMap(fa)(f)
      }
  }

  val bridge: CoreBridge.Of[dsl.type]

  import dsl.{-⚬, |*|, |+|, Done, Ping}
  import bridge.*

  type ExecutionParam[A]
  type ExecutionParams[A] = libretto.exec.ExecutionParams[ExecutionParam, A]

  extension (using exn: Execution, pos: SourcePos)(port: exn.OutPort[Done]) {
    def expectDone: Outcome[Unit] =
      port.awaitDone().map {
        case Left(e)   => TestResult.crash(e)
        case Right(()) => TestResult.success(())
      }

    def expectCrashDone: Outcome[Throwable] =
      port.awaitDone().map {
        case Left(e)   => TestResult.success(e)
        case Right(()) => TestResult.failed(using pos)("Expected crash, but got Done")
      }
  }

  extension (using exn: Execution, pos: SourcePos)(port: exn.OutPort[Ping]) {
    def expectPing: Outcome[Unit] =
      port.awaitPing().map {
        case Left(e)   => TestResult.crash(e)
        case Right(()) => TestResult.success(())
      }

    def expectNoPingFor(duration: FiniteDuration): Outcome[exn.OutPort[Ping]] =
      port.awaitNoPing(duration).map {
        case Left(Left(e))   => TestResult.crash(e)
        case Left(Right(())) => TestResult.failed(using pos)(s"Expected no Ping for $duration, but got Ping")
        case Right(port)     => TestResult.success(port)
      }

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
      port.awaitEither().map {
        case Left(e)         => TestResult.crash(e)
        case Right(Left(p))  => TestResult.success(p)
        case Right(Right(_)) => TestResult.failed(using pos)("Expected Left, but got Right")
      }

    def expectRight: Outcome[exn.OutPort[B]] =
      port.awaitEither().map {
        case Left(e)         => TestResult.crash(e)
        case Right(Left(_))  => TestResult.failed(using pos)("Expected Right, but got Left")
        case Right(Right(p)) => TestResult.success(p)
      }
  }
}

object TestKit extends TestKitOps

trait TestKitOps {
  transparent inline def givenInstance(using kit: TestKit): kit.type =
    kit

  transparent inline def dsl(using kit: TestKit): kit.dsl.type =
    kit.dsl

  transparent inline def bridge(using kit: TestKit): kit.bridge.type =
    kit.bridge
}
