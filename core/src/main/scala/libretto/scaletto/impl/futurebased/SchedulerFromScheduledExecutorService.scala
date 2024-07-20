package libretto.scaletto.impl.futurebased

import java.util.concurrent.ScheduledExecutorService
import libretto.util.Scheduler
import scala.concurrent.duration.FiniteDuration

class SchedulerFromScheduledExecutorService(
    scheduler: ScheduledExecutorService,
) extends Scheduler {
  override def schedule(d: FiniteDuration, f: () => Unit): Unit =
    scheduler.schedule((() => f()): Runnable, d.length, d.unit)
}
