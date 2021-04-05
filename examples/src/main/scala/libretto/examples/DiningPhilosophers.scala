package libretto.examples

import libretto.StarterApp
import scala.concurrent.duration._
import scala.util.Random

object DiningPhilosophers extends StarterApp {
  object Forks {
    private type HeldForkF[SharedFork] = Done |*| Delayed[SharedFork]

    private type SharedForkF[X] = Done |&| (HeldForkF[X] |+| X)

    opaque type SharedFork = Rec[SharedForkF]

    opaque type HeldFork = HeldForkF[SharedFork]

    implicit def signalingJunctionSharedFork: SignalingJunction.Negative[SharedFork] =
      SignalingJunction.Negative.from(
        Signaling.Negative.rec(Signaling.Negative.choice),
        Junction.Negative.rec(rec => Junction.Negative.delayChoice(
          Junction.invert(Junction.Positive.junctionDone),
          Junction.Negative.delegateToEither(
            Junction.Negative.byFst(Junction.invert(Junction.Positive.junctionDone)),
            rec,
          ),
        ))
      )

    def putDown: HeldFork -⚬ SharedFork =
      Delayed.triggerBy

    def releaseFork: SharedFork -⚬ Done =
      unpack > chooseL

    def pickUp: SharedFork -⚬ (HeldFork |+| SharedFork) =
      unpack > chooseR

    def useForks(f: Done -⚬ Done): (HeldFork |*| HeldFork) -⚬ (HeldFork |*| HeldFork) =
      IXI > par(join > f > fork, id) > IXI

    def useForksL[A, B](
      f: A -⚬ B,
    )(implicit
      A: Junction.Positive[A],
      B: Signaling.Positive[B],
    ): (A |*| (HeldFork |*| HeldFork)) -⚬ (B |*| (HeldFork |*| HeldFork)) =
      id[ A |*| (HeldFork |*| HeldFork) ]           .to[  A |*| ((Done |*| Delayed[SharedFork])  |*| (Done |*| Delayed[SharedFork])) ]
        .>.snd(IXI)                                 .to[  A |*| ((Done |*| Done)  |*| (Delayed[SharedFork] |*| Delayed[SharedFork])) ]
        .>.snd.fst(join).assocRL                    .to[ (A |*|       Done      ) |*| (Delayed[SharedFork] |*| Delayed[SharedFork])  ]
        .>.fst(A.awaitPosSnd > f > B.signalPosSnd)  .to[ (B |*|       Done      ) |*| (Delayed[SharedFork] |*| Delayed[SharedFork])  ]
        .assocLR.>.snd.fst(fork)                    .to[  B |*| ((Done |*| Done)  |*| (Delayed[SharedFork] |*| Delayed[SharedFork])) ]
        .>.snd(IXI)                                 .to[  B |*| ((Done |*| Delayed[SharedFork])  |*| (Done |*| Delayed[SharedFork])) ]

    private def singleOwnerFork: Done -⚬ SharedFork = rec { self =>
      val pickUp: Done -⚬ HeldFork =
        introSnd(Delayed(self))

      choice(id, pickUp > injectL) > pack[SharedForkF]
    }

    def makeSharedFork: Done -⚬ (SharedFork |*| SharedFork) = rec { makeSharedFork =>
      val caseFstReleases: Done -⚬ (Done |*| SharedFork) =
        fork(id, singleOwnerFork)

      val caseFstPicksUp: Done -⚬ ((HeldFork |+| SharedFork) |*| SharedFork) = {
        val go: One -⚬ (Delayed[SharedFork] |*| SharedFork) = rec { go =>
          val caseFstPutsDown: One -⚬ (Delayed[SharedFork] |*| SharedFork) =
            Delayed.fst(makeSharedFork)

          val caseSndReleases: One -⚬ (Delayed[SharedFork] |*| Done) =
            Delayed(singleOwnerFork) > introSnd(done)

          val caseSndPicksUp: One -⚬ (Delayed[SharedFork] |*| (HeldFork |+| SharedFork)) =
            go > par(id, injectR)

          val caseSndActs: One -⚬ (Delayed[SharedFork] |*| SharedFork) =
            choice(caseSndReleases, caseSndPicksUp) > coDistributeL > par(id, pack[SharedForkF])

          choice(caseFstPutsDown, caseSndActs) > select
        }

        introSnd(go).assocRL > par(injectL, id)
      }

      val caseFstWins: Done -⚬ (SharedFork |*| SharedFork) =
        choice(caseFstReleases, caseFstPicksUp) > coDistributeR > par(pack[SharedForkF], id)

      val caseSndWins: Done -⚬ (SharedFork |*| SharedFork) =
        caseFstWins > swap

      choice(caseFstWins, caseSndWins) > select
    }
  }

  import Forks._

  object Philosopher {
    type Name = Val[String]

    private def log(f: String => String): Name -⚬ Name =
      dup[String].awaitSnd(mapVal[String, String](f) > printLine)

    def think: (Name |*| (SharedFork |*| SharedFork)) -⚬ (Name |*| (SharedFork |*| SharedFork)) = {
      implicit val bothForksJunction: Junction.Positive[SharedFork |*| SharedFork] =
        Junction.invert(Junction.Negative.both[SharedFork, SharedFork])

      id[Name |*| (SharedFork |*| SharedFork)]
        .>.fst(log(name => s"😴 $name falling asleep"))
        .>.fst(delayUsing(randomDelay))
        .>.fst(log(name => s"🔔 $name wakes up"))
        .>.fst.signalSnd
        .assocLR
        .>.snd.awaitFst
    }

    def eat: (Name |*| (HeldFork |*| HeldFork)) -⚬ (Name |*| (HeldFork |*| HeldFork)) =
      useForksL(log(name => s"${Console.GREEN}🍝 $name eating${Console.RESET}") > delayUsing(randomDelay))

    /** Results in left if managed to eat, right if not (failed to pick up one of the forks). */
    def tryEat: (Name |*| (SharedFork |*| SharedFork)) -⚬ ((Name |*| (SharedFork |*| SharedFork)) |+| (Name |*| (SharedFork |*| SharedFork))) = {
      // continuation after successfully picking up the left fork
      val go1: (Name |*| (HeldFork |*| SharedFork)) -⚬ ((Name |*| (SharedFork |*| SharedFork)) |+| (Name |*| (SharedFork |*| SharedFork))) =
        id                                       [  Name |*| ( HeldFork   |*|         SharedFork                                    ) ]
          .>.snd.snd(pickUp)                  .to[  Name |*| ( HeldFork   |*| (HeldFork    |+|                           SharedFork)) ]
          .>.snd(distributeL)                 .to[  Name |*| ((HeldFork   |*| HeldFork  )  |+|           (HeldFork   |*| SharedFork)) ]
          .distributeL                        .to[ (Name |*|  (HeldFork   |*| HeldFork  )) |+| (Name |*| (HeldFork   |*| SharedFork)) ]
          .>.left(eat)                        .to[ (Name |*|  (HeldFork   |*| HeldFork  )) |+| (Name |*| (HeldFork   |*| SharedFork)) ]
          .>.left.snd(par(putDown, putDown))  .to[ (Name |*|  (SharedFork |*| SharedFork)) |+| (Name |*| (HeldFork   |*| SharedFork)) ]
          .>.right.snd.fst(putDown)           .to[ (Name |*|  (SharedFork |*| SharedFork)) |+| (Name |*| (SharedFork |*| SharedFork)) ]

      id                                         [  Name |*| (                         SharedFork                    |*| SharedFork ) ]
        .>.snd.fst(pickUp)                    .to[  Name |*| ((HeldFork                    |+|           SharedFork) |*| SharedFork ) ]
        .>.snd(distributeR)                   .to[  Name |*| ((HeldFork   |*| SharedFork)  |+|           (SharedFork |*| SharedFork)) ]
        .distributeL                          .to[ (Name |*|  (HeldFork   |*| SharedFork)) |+| (Name |*| (SharedFork |*| SharedFork)) ]
        .either(go1, injectR)                 .to[ (Name |*|  (SharedFork |*| SharedFork)) |+| (Name |*| (SharedFork |*| SharedFork)) ]
    }

    def eatOnce: (Name |*| (SharedFork |*| SharedFork)) -⚬ (Name |*| (SharedFork |*| SharedFork)) = rec { eatOnce =>
      tryEat > either(id, think > eatOnce)
    }

    def run(cycles: Int): (Name |*| (SharedFork |*| SharedFork)) -⚬ Done = {
      val go: (Val[Int] |*| (Name |*| (SharedFork |*| SharedFork))) -⚬ Done = rec { go =>
        val complete: (Done |*| (Name |*| (SharedFork |*| SharedFork))) -⚬ Done =
          par(id, par(neglect, par(releaseFork, releaseFork) > join) > join) > join

        val eatThinkAndRepeat: (Val[Int] |*| (Name |*| (SharedFork |*| SharedFork))) -⚬ Done =
          par(id, eatOnce > think) > go

        id                                                           [        Val[Int]  |*| (Name |*| (SharedFork |*| SharedFork))  ]
          .>.fst(dec)                                             .to[ PMaybe[Val[Int]] |*| (Name |*| (SharedFork |*| SharedFork))  ]
          .>(PMaybe.switchWithR(complete, eatThinkAndRepeat))     .to[                 Done                                         ]
      }

      introFst(const(cycles)) > go
    }

    private val randomDelay: Done -⚬ Done =
      constVal(()) > mapVal(_ => Random.between(1000, 3000).millis) > delay

    /** Decrements an integer. If the result would be negative, results in [[Done]] on the left,
     *  otherwise results in the decremented integer on the right.
     */
    private val dec: Val[Int] -⚬ PMaybe[Val[Int]] =
      mapVal[Int, Option[Int]] {
        case i if i > 0 => Some(i - 1)
        case _          => None
      } > optionToPMaybe
  }

  import Philosopher.Name

  override def blueprint: Done -⚬ Done = {
    val names: Done -⚬ LList1[Val[String]] =
      constList1Of("Aristotle", "Bolzano", "Confucius", "Descartes", "Epictetus")

    names                                                     .to[ LList1[                               Name ] ]
      .>(LList1.map(introFst(done > makeSharedFork).assocLR)) .to[ LList1[SharedFork |*| (SharedFork |*| Name)] ]
      .>(LList1.halfRotateL)                                  .to[ LList1[(SharedFork |*| Name) |*| SharedFork] ]
      .>(LList1.map(par(swap, id).assocLR))                   .to[ LList1[Name |*| (SharedFork |*| SharedFork)] ]
      .>(LList1.map(Philosopher.run(cycles = 5)))             .to[ LList1[     Done                           ] ]
      .>(LList1.fold)                                         .to[      Done                                    ]
  }
}
