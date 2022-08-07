package libretto.testing

import libretto.ExecutionParams

trait ManualClockParams[P[_]] extends ExecutionParams[P] {
  def manualClock: P[ManualClock]
}
