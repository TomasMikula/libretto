package libretto.testing

import libretto.lambda.util.SourcePos
import scala.{:: => NonEmptyList}
import scala.concurrent.duration.FiniteDuration

enum TestResult[A] {
  import TestResult.Failure

  case Success(value: A)
  case Failures(value: NonEmptyList[TestResult.Failure])

  def map[B](f: A => B): TestResult[B] =
    this match {
      case Success(a)   => Success(f(a))
      case Failures(es) => Failures(es)
    }

  def flatMap[B](f: A => TestResult[B]): TestResult[B] =
    this match {
      case Success(a)   => f(a)
      case Failures(es) => Failures(es)
    }

  def zipWith[B, C](that: TestResult[B])(f: (A, B) => C): TestResult[C] =
    (this, that) match {
      case (Success(a), Success(b))         => Success(f(a, b))
      case (Success(_), Failures(y))        => Failures(y)
      case (Failures(x), Success(_))        => Failures(x)
      case (Failures(x :: xs), Failures(y)) => Failures(NonEmptyList(x, xs ++ y))
    }
}

object TestResult {
  enum Failure {
    case Failed(msg: String, pos: SourcePos, error: Option[Throwable])
    case Crash(error: Throwable)
    case TimedOut(duration: FiniteDuration)
  }

  def success[A](a: A): TestResult[A] =
    Success(a)

  def failures[A](e: Failure, es: Failure*): TestResult[A] =
    Failures(NonEmptyList(e, es.toList))

  def failed[A](using pos: SourcePos)(
    msg: String,
    error: Option[Throwable] = None,
  ): TestResult[A] =
    failures(Failure.Failed(msg, pos, error))

  def crash[A](e: Throwable): TestResult[A] =
    failures(Failure.Crash(e))

  def timedOut[A](duration: FiniteDuration): TestResult[A] =
    failures(Failure.TimedOut(duration))
}
