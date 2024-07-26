package libretto.exec

import libretto.util.Scheduler

trait SupportsCustomScheduler[P[_]] {
  def scheduler(scheduler: Scheduler): P[Unit]
}
