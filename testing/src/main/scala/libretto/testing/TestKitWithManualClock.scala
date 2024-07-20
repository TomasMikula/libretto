package libretto.testing

trait TestKitWithManualClock extends TestKit {
  def manualClockParam: ExecutionParam[ManualClock]

  def manualClock: ExecutionParams[ManualClock] =
    libretto.ExecutionParams.wrap(manualClockParam)
}
