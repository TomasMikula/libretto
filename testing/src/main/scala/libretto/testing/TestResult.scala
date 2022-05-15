package libretto.testing

enum TestResult[A] {
  case Success(value: A)
  case Failure(msg: String)
  case Crash(error: Throwable)
}

object TestResult {
  def success[A](a: A): TestResult[A] =
    Success(a)

  def failure[A](msg: String): TestResult[A] =
    Failure(msg)

  def crash[A](e: Throwable): TestResult[A] =
    Crash(e)
}
