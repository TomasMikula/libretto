package libretto.examples.diningPhilosophers

import libretto.StarterKit._
import libretto.StarterKit.$._

object ForksProvider extends Forks {
  opaque override type SharedFork = Lock

  opaque override type HeldFork = AcquiredLock

  override def tryPickUp: SharedFork -⚬ (HeldFork |+| SharedFork) =
    Lock.tryAcquire

  override def letGo: SharedFork -⚬ Done =
    Lock.close

  override def putDown: HeldFork -⚬ SharedFork =
    AcquiredLock.release

  override def heldForkReadiness: SignalingJunction.Positive[HeldFork] =
    AcquiredLock.acquisition

  def mkSharedFork: Done -⚬ (SharedFork |*| SharedFork) =
    Lock.newLock > Lock.share
}
