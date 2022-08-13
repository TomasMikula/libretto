package libretto.testing

import libretto.util.SourcePos

enum TestResult[A] {
  case Success(value: A)
  case Failure(msg: String, pos: SourcePos)
  case Crash(error: Throwable)
}

object TestResult {
  def success[A](a: A): TestResult[A] =
    Success(a)

  def failure[A](using pos: SourcePos)(msg: String): TestResult[A] =
    Failure(msg, pos)

  def crash[A](e: Throwable): TestResult[A] =
    Crash(e)
}
