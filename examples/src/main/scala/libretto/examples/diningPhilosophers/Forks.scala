package libretto.examples.diningPhilosophers

import libretto.StarterKit._
import libretto.StarterKit.$._

trait Forks {
  /** Interface to a fork. The fork itself may be shared among multiple philosophers,
    * in which case multiple [[SharedFork]]s coordinate to access a single "physical" fork.
    * [[SharedFork]] must be successfully picked up (see [[tryPickUp]]) before it can be used to eat.
    */
  type SharedFork

  /** A fork that has been successfully picked up and can be used.
    * It represents exclusive access to a fork.
    */
  type HeldFork

  /** Attempts to pick up a shared fork. If successful, outputs [[HeldFork]] on the left.
    * Does not wait for the shared fork to become available.
    */
  def tryPickUp: SharedFork -⚬ (HeldFork |+| SharedFork)

  /** Releases the fork so that it can be acquired by others. */
  def putDown: HeldFork -⚬ SharedFork

  /** Gives up access to the fork. */
  def letGo: SharedFork -⚬ Done

  /** Ability to signal when [[HeldFork]] is ready (picked up or done being used). */
  implicit def signalingHeldFork: Signaling.Positive[HeldFork]

  /** Ability of [[HeldFork]] to await a [[Done]] signal, thereby deferring [[HeldFork]]'s readiness. */
  implicit def junctionHeldFork: Junction.Positive[HeldFork]

  /** Ability to defer the next action ([[tryPickUp]] or [[letGo]]) on [[SharedFork]]. */
  implicit def deferrableSharedFork: Deferrable.Positive[SharedFork]
}
