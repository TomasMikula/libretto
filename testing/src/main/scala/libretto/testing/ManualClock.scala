package libretto.testing

import libretto.Scheduler
import scala.annotation.tailrec
import scala.concurrent.{ExecutionContext, Future, Promise}
import scala.concurrent.duration.{FiniteDuration, DurationInt}
import scala.collection.mutable.PriorityQueue

trait ManualClock {
  def advanceBy(d: FiniteDuration): Unit

  /** Advances the time to the given amount from the start.
    * If the current time is already past that amount, does nothing.
    */
  def advanceTo(d: FiniteDuration): Unit
}

object ManualClock {
  /**
    * @param ec where to execute scheduled actions once fired.
    */
  def scheduler(): (ManualClock, Scheduler) = {
    val s = new ManualScheduler
    (s, s)
  }

  private class ManualScheduler extends ManualClock with Scheduler {
    import ManualScheduler.ScheduledAction

    val queue: PriorityQueue[ScheduledAction] =
      PriorityQueue.empty

    var now: FiniteDuration = 0.seconds

    override def schedule(
      delay: FiniteDuration,
      action: () => Unit,
    ): Unit = {
      if (delay.length == 0L) {
        action()
      } else {
        this.synchronized {
          queue.addOne(ScheduledAction(
            fireAt = now + delay,
            action,
          ))
        }
      }
    }

    override def advanceTo(time: FiniteDuration): Unit = {
      this.synchronized {
        if (time <= this.now) {
          // do nothing
        } else {
          this.now = time
        }
      }
      fireExpired()
    }

    override def advanceBy(d: FiniteDuration): Unit = {
      this.synchronized {
        this.now += d
      }
      fireExpired()
    }

    @tailrec
    private def fireExpired(): Unit = {
      val action =
        this.synchronized {
          if (this.queue.nonEmpty && this.queue.head.fireAt <= this.now) {
            this.queue.dequeue()
          } else {
            null
          }
        }
      if (action != null) {
        action.action()
        fireExpired()
      }
    }
  }

  private object ManualScheduler {
    private[ManualScheduler] case class ScheduledAction(
      fireAt: FiniteDuration,
      action: Function0[Unit],
    )
    private[ManualScheduler] object ScheduledAction {
      given Ordering[ScheduledAction] =
        Ordering.by[ScheduledAction, FiniteDuration](_.fireAt).reverse
    }
  }
}
