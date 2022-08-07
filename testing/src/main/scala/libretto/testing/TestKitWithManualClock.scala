package libretto.testing

trait TestKitWithManualClock extends TestKit {
  override val ExecutionParam: ManualClockParams[ExecutionParam]
}
