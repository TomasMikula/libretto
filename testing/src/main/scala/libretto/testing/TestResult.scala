package libretto.testing

import libretto.lambda.util.SourcePos
import scala.concurrent.duration.FiniteDuration

enum TestResult[A] {
  case Success(value: A)
  case Failure(msg: String, pos: SourcePos, error: Option[Throwable])
  case Crash(error: Throwable)
  case TimedOut(duration: FiniteDuration) extends TestResult[A]

  def flatMap[B](f: A => TestResult[B]): TestResult[B] =
    this match {
      case Success(a)       => f(a)
      case Failure(m, p, e) => Failure(m, p, e)
      case Crash(error)     => Crash(error)
      case TimedOut(d)      => TimedOut(d)
    }
}

object TestResult {
  def success[A](a: A): TestResult[A] =
    Success(a)

  def failure[A](using pos: SourcePos)(
    msg: String,
    error: Option[Throwable] = None,
  ): TestResult[A] =
    Failure(msg, pos, error)

  def crash[A](e: Throwable): TestResult[A] =
    Crash(e)
}
