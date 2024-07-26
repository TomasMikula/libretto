package libretto.testing

trait TestKitWithManualClock extends TestKit {
  def manualClockSupport: SupportsManualClock[ExecutionParam]

  def manualClock: ExecutionParams[ManualClock] =
    libretto.exec.ExecutionParams.wrap(manualClockSupport.manualClock)
}

trait SupportsManualClock[P[_]]:
  def manualClock: P[ManualClock]
