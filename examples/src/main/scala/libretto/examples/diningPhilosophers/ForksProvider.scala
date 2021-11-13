package libretto.examples.diningPhilosophers

import libretto.StarterKit._
import libretto.StarterKit.$._

object ForksProvider extends Forks {
  private type HeldForkF[SharedFork] = Done |*| Detained[SharedFork]

  private type SharedForkF[X] = Done |&| (HeldForkF[X] |+| X)

  opaque override type SharedFork = Rec[SharedForkF]

  opaque override type HeldFork = HeldForkF[SharedFork]

  override def tryPickUp: SharedFork -⚬ (HeldFork |+| SharedFork) =
    unpack[SharedForkF] > chooseR

  override def letGo: SharedFork -⚬ Done =
    unpack[SharedForkF] > chooseL

  override def putDown: HeldFork -⚬ SharedFork =
    Detained.releaseBy

  override def heldForkReadiness: SignalingJunction.Positive[HeldFork] =
    SignalingJunction.Positive.byFst

  def mkSharedFork: Done -⚬ (SharedFork |*| SharedFork) =
    rec { makeSharedFork =>
      val caseFstReleases: Done -⚬ (Done |*| SharedFork) =
        forkMap(id, singleOwnerFork)

      val caseFstPicksUp: Done -⚬ ((HeldFork |+| SharedFork) |*| SharedFork) = {
        val go: One -⚬ (Detained[SharedFork] |*| SharedFork) = rec { go =>
          val caseFstPutsDown: One -⚬ (Detained[SharedFork] |*| SharedFork) =
            Detained.fst(makeSharedFork)

          val caseSndReleases: One -⚬ (Detained[SharedFork] |*| Done) =
            Detained.thunk(singleOwnerFork) > introSnd(done)

          val caseSndPicksUp: One -⚬ (Detained[SharedFork] |*| (HeldFork |+| SharedFork)) =
            go > par(id, injectR)

          val caseSndActs: One -⚬ (Detained[SharedFork] |*| SharedFork) =
            choice(caseSndReleases, caseSndPicksUp) > coDistributeL > par(id, pack[SharedForkF])

          choice(caseFstPutsDown, caseSndActs) > selectBy(Detained.notifyReleaseNeg, notifyAction)
        }

        introSnd(go).assocRL > par(injectL, id)
      }

      val caseFstWins: Done -⚬ (SharedFork |*| SharedFork) =
        choice(caseFstReleases, caseFstPicksUp) > coDistributeR > par(pack[SharedForkF], id)

      val caseSndWins: Done -⚬ (SharedFork |*| SharedFork) =
        caseFstWins > swap

      choice(caseFstWins, caseSndWins) > selectBy(notifyAction, notifyAction)
    }

  private def singleOwnerFork: Done -⚬ SharedFork = rec { self =>
    val pickUp: Done -⚬ HeldFork =
      introSnd(Detained.thunk(self))

    choice(id, pickUp > injectL) > pack[SharedForkF]
  }

  /** Notifies via [[Pong]] signal when action ([[tryPickUp]] or [[letGo]]) is performed
    * on the output [[SharedFork]].
    */
  private def notifyAction: (Pong |*| SharedFork) -⚬ SharedFork =
    snd(unpack[SharedForkF]) > |&|.notify > pack[SharedForkF]
}
