package libretto.examples.diningPhilosophers

import libretto.StarterKit._
import libretto.StarterKit.$._
import scala.concurrent.duration._
import scala.util.Random

object Philosophers {
  def apply(forks: Forks): Philosophers[forks.type] =
    new Philosophers[forks.type](forks)
}

class Philosophers[ForksImpl <: Forks](val forks: ForksImpl) {
  import forks._

  /** A philosopher is given access to two shared forks (each of them shared with one neighbor).
    *
    * @param name name of the philosopher
    * @param cycles number of times the philosopher will eat
    */
  def behavior(name: String)(cycles: Int): (SharedFork |*| SharedFork) -⚬ Done =
    λ { (forks: $[SharedFork |*| SharedFork]) =>
      // generate a (constant) libretto function from the meta-level value `cycles`
      val constCycles: One -⚬ Val[Int] =
        const(cycles)

      val (forks1 |*| (n: $[Val[Int]])) =
        forks also constCycles

      run(name)(n |*| forks1)
    }

  private def run(name: String): (Val[Int] |*| (SharedFork |*| SharedFork)) -⚬ Done = rec { run =>
    λ { case (cycles |*| forks) =>
      // decrement the number of cycles and then "pattern match" on the result
      (dec(cycles) |*| forks) > PMaybe.switchWithR(
        caseNone =
          // cycles was already 0
          λ { case (done |*| (fork1 |*| fork2)) =>
            join(done |*| join(letGo(fork1) |*| letGo(fork2)))
          },
        caseSome =
          λ { case (remainingCycles |*| forks) =>
            val (eaten |*| (fork1 |*| fork2)) = eatOnce(name)(forks)
            val thought = when(eaten) { think(name) }

            // prevent the recursive call to proceed concurrently to thinking by
            // delaying the remaining cycles value until thinking has finished
            run((remainingCycles waitFor thought) |*| (fork1 |*| fork2))
          }
      )
    }
  }

  private def think(name: String): Done -⚬ Done =
    printLine(s"😴 $name falling asleep") > randomDelay > printLine(s"🔔 $name wakes up")

  private def eatOnce(name: String): (SharedFork |*| SharedFork) -⚬ (Done |*| (SharedFork |*| SharedFork)) = rec { eatOnce =>
    tryEat(name) > |+|.signalR > either(
      caseLeft =
        // succeeded in picking up both forks and ate
        id[Done |*| (SharedFork |*| SharedFork)],
      caseRight =
        // failed to pick up the forks; think for a bit and then try again
        λ { case ((failed: $[Done]) |*| (lFork |*| rFork)) =>
          val (thought |*| thoughtPing) = when(failed) { think(name) > notifyDoneR }
          val (lPing |*| rPing) = thoughtPing > split
          val (eaten |*| forks) =
            eatOnce((lFork deferUntil lPing) |*| (rFork deferUntil rPing))
          join(thought |*| eaten) |*| forks
        }
    )
  }

  /** Results in left if managed to eat, right if not (failed to pick up one of the forks). */
  private def tryEat(name: String): (SharedFork |*| SharedFork) -⚬ ((Done |*| (SharedFork |*| SharedFork)) |+| (SharedFork |*| SharedFork)) =
    λ { case (lFork |*| rFork) =>
      // try to pick up the left fork and then "pattern match" on the result
      (tryPickUp(lFork) |*| rFork) > |+|.switchWithR(
        caseLeft =
          // succeeded to pick up the left fork
          λ { case (lHeldFork |*| rFork) =>
            // try to pick up the right fork and then "pattern match" on the result
            (lHeldFork |*| tryPickUp(rFork)) > |+|.switchWithL(
              caseLeft =
                // succeeded to pick up the right fork
                λ { case (lHeldFork |*| rHeldFork) =>
                  // eat with forks, then put down the forks and return success (via `injectL`)
                  eat(name)(lHeldFork |*| rHeldFork) > λ { case (eaten |*| (lhf |*| rhf)) =>
                    injectL(eaten |*| (putDown(lhf) |*| putDown(rhf)))
                  }
                },
              caseRight =
                // failed to pick up the right fork
                λ { case (lHeldFork |*| rFork) =>
                  injectR(putDown(lHeldFork) |*| rFork)
                },
            )
          },
        caseRight =
          // failed to pick up the left fork
          λ { case (lFork |*| rFork) =>
            injectR(lFork |*| rFork)
          }
      )
    }

  private def eat(name: String): (HeldFork |*| HeldFork) -⚬ (Done |*| (HeldFork |*| HeldFork)) =
    λ { case (lFork |*| rFork) =>
      val (lFork1 |*| lReady) = lFork > signalDone
      val (rFork1 |*| rReady) = rFork > signalDone

      val eaten: $[Done] =
        // eat only after both forks are ready
        when(join(lReady |*| rReady)) {
          printLine(s"${Console.GREEN}🍝 $name eating${Console.RESET}") > randomDelay
        }

      // split the `eaten` Done signal into three
      val (done |*| (lDone |*| rDone)) =
        eaten > (id /\ (id /\ id))

      // hold up the forks until eating is done
      (done |*| ((lFork1 waitFor lDone) |*| (rFork1 waitFor rDone)))
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
