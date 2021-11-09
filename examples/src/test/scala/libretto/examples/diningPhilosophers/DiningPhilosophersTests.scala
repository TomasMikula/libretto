package libretto.examples.diningPhilosophers

import libretto.testing.TestSuite

class DiningPhilosophersTests extends TestSuite {
  import kit.dsl._
  import kit.dsl.$._
  import kit.coreLib._
  import kit.scalaLib._

  import ForksProvider.{HeldFork, letGo, mkSharedFork, putDown, tryPickUp}

  given Signaling.Positive[HeldFork] =
    ForksProvider.signalingHeldFork

  given deferrableHeldFork: Deferrable.Positive[HeldFork] =
    ForksProvider.junctionHeldFork

  test("SharedFork: successful pick up (left)") {
    val prg: Done -⚬ Done =
      mkSharedFork > par(
        tryPickUp > assertLeft > putDown > letGo,
        letGo,
      ) > join

    assertCompletes(prg)
  }

  test("SharedFork cannot be picked up twice") {
    val prg: Done -⚬ Done =
      λ { start =>
        val (lFork |*| rFork) =
          mkSharedFork(start)

        val (heldRFork |*| rAcquired) =
          tryPickUp(rFork) > assertLeft > notifyPosSnd

        val (lFork1 |*| lAttempted) =
          (lFork blockUntil rAcquired) > tryPickUp > notifyPosSnd > fst(assertRight)

        join( letGo(lFork1)
          |*| letGo(putDown(heldRFork deferUntil lAttempted))
        )
      }

    assertCompletes(prg)
  }
}
