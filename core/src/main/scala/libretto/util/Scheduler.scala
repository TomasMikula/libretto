package libretto.util

import scala.concurrent.duration.FiniteDuration

trait Scheduler {
  def schedule(
    delay: FiniteDuration,
    action: () => Unit,
  ): Unit
}
