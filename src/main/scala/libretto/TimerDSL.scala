package libretto

import scala.concurrent.duration.FiniteDuration

trait TimerDSL extends CoreDSL {
  def delay(d: FiniteDuration): Done -⚬ Done
}
