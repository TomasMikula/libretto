package libretto.examples.diningPhilosophers

import libretto.scaletto.StarterKit.dsl.*
import libretto.scaletto.StarterKit.dsl.$.*
import libretto.scaletto.StarterKit.puroLib.*
import libretto.scaletto.StarterKit.crashLib.*
import libretto.testing.scaletto.StarterTestKit
import libretto.testing.scalatest.scaletto.ScalatestStarterTestSuite
import libretto.testing.TestCase

class DiningPhilosophersTests extends ScalatestStarterTestSuite {

  import ForksProvider.{HeldFork, letGo, mkSharedFork, putDown, tryPickUp}

  given heldForkReadiness: SignalingJunction.Positive[HeldFork] =
    ForksProvider.heldForkReadiness

  override def testCases(using kit: StarterTestKit): List[(String, TestCase[kit.type])] =
    List(
      "SharedFork: successful pick up (left)" -> TestCase.awaitDone {
        val prg: Done -⚬ Done =
          mkSharedFork > par(
            tryPickUp > leftOrCrash("Failed to pick up the fork.") > putDown > letGo,
            letGo,
          ) > join

        prg
      },

      "SharedFork cannot be picked up twice" -> TestCase.awaitDone {
        val prg: Done -⚬ Done =
          λ { start =>
            val (lFork |*| rFork) =
              mkSharedFork(start)

            val (heldRFork |*| rAcquired) =
              tryPickUp(rFork) > leftOrCrash("Failed to pick up the fork.") > notifyPosSnd

            val (lFork1 |*| lAttempted) =
              (lFork blockUntil rAcquired) > tryPickUp > notifyPosSnd > fst(rightOrCrash("Succeeded in picking up shared fork twice simultaneously"))

            join( letGo(lFork1)
              |*| letGo(putDown(heldRFork deferUntil lAttempted))
            )
          }

        prg
      },
    )
}
