package libretto.testing

enum TestResult {
  case Success
  case Failure(msg: String)
  case Crash(error: Throwable)
}
