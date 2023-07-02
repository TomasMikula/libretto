package libretto.examples.diningPhilosophers

import libretto.scaletto.StarterKit.dsl.*
import libretto.scaletto.StarterKit.dsl.$.*
import libretto.scaletto.StarterKit.coreLib.*
import libretto.testing.scaletto.StarterTestKit
import libretto.testing.scalatest.scaletto.ScalatestStarterTestSuite
import libretto.testing.TestCase

class DiningPhilosophersTests extends ScalatestStarterTestSuite {

  import ForksProvider.{HeldFork, letGo, mkSharedFork, putDown, tryPickUp}

  given heldForkReadiness: SignalingJunction.Positive[HeldFork] =
    ForksProvider.heldForkReadiness

  override def testCases(using kit: StarterTestKit): List[(String, TestCase[kit.type])] = {
    import kit.{leftOrCrash, rightOrCrash, success}

    List(
      "SharedFork: successful pick up (left)" -> TestCase {
        val prg: Done -⚬ Done =
          mkSharedFork > par(
            tryPickUp > leftOrCrash("Failed to pick up the fork.") > putDown > letGo,
            letGo,
          ) > join

        prg > success
      },

      "SharedFork cannot be picked up twice" -> TestCase {
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

        prg > success
      },
    )
  }
}
