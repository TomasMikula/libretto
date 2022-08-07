package libretto

import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration.FiniteDuration

trait Scheduler {
  // TODO: don't return Future
  def schedule[A](
    delay: FiniteDuration,
    action: () => A,
  )(using ExecutionContext): Future[A]
}
