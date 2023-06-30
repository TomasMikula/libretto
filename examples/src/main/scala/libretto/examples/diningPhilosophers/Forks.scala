package libretto.examples.diningPhilosophers

import libretto.scaletto.StarterKit.*
import libretto.scaletto.StarterKit.$.*

trait Forks {
  /** Interface to a fork. The fork itself may be shared among multiple philosophers,
    * in which case multiple [[SharedFork]] interfaces are created for one "physical" fork.
    * These [[SharedFork]]s then have to coordinate when accessing the underlying "physical" fork.
    * Once [[SharedFork]] is successfully picked up from the table (see [[tryPickUp]]), the holder
    * of the resulting [[HeldFork]] can use it to eat.
    */
  type SharedFork

  /** A fork that has been successfully picked up and can be used.
    * It represents exclusive access to a fork.
    */
  type HeldFork

  /** Attempts to pick up a shared fork. If successful, outputs [[HeldFork]] on the left.
    * Does not wait for the shared fork to become available. If it is unavailable,
    * outputs [[SharedFork]] on the right.
    */
  def tryPickUp: SharedFork -⚬ (HeldFork |+| SharedFork)

  /** Releases the fork so that it can be acquired by others. */
  def putDown: HeldFork -⚬ SharedFork

  /** Gives up access to the fork. */
  def letGo: SharedFork -⚬ Done

  /** Ability of [[HeldFork]] to
    *  - signal readiness (when picked up or done being used).
    *  - defer readiness by awaiting a [[Done]] signal.
    */
  given heldForkReadiness: SignalingJunction.Positive[HeldFork]
}
