package libretto.examples.diningPhilosophers

import libretto.scaletto.StarterKit.*

/** Implements `Forks`.
  * Internally, it represents a fork as a lock from the core library.
  * (Note that the [[Lock]] from the core library is not a primitive itself,
  * but is implemented using other primitives. Racing plays a key role
  * in that implementation.)
  */
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
