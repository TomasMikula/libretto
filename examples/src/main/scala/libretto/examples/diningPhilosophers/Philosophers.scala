package libretto.examples.diningPhilosophers

import libretto.scaletto.StarterKit.*
import scala.concurrent.duration.*
import scala.util.Random

object Philosophers {
  def apply(forks: Forks): Philosophers[forks.type] =
    new Philosophers[forks.type](forks)
}

class Philosophers[ForksImpl <: Forks](val forks: ForksImpl) {
  import forks.*

  /** A philosopher is given access to two shared forks (each of them shared with one neighbor).
    * When a philosopher finishes, it produces a [[Done]] signal.
    *
    * @param name name of the philosopher
    * @param cycles number of times the philosopher will eat
    */
  def behavior(name: String)(cycles: Int): (SharedFork |*| SharedFork) -⚬ Done = {
    // turn the meta-level value `cycles` into a constant libretto expression
    def constCycles(using LambdaContext): $[Val[Int]] =
      $.one > const(cycles)

    λ { (forks: $[SharedFork |*| SharedFork]) =>
      run(name)(forks |*| constCycles)
    }
  }

  private def run(name: String): ((SharedFork |*| SharedFork) |*| Val[Int]) -⚬ Done =
    rec { run =>
      λ { case (forks |*| cycles) =>
        // decrement the number of cycles and then "pattern match" on the result
        (dec(cycles) |*| forks) > PMaybe.switchWithR(
          caseNone =
            // cycles was already 0
            λ { case (done |*| (fork1 |*| fork2)) =>
              // let the forks go and just join the resulting `Done` signals
              join(done |*| join(letGo(fork1) |*| letGo(fork2)))
            },
          caseSome =
            // cycles was >0, the philospher wants to eat
            λ { case (remainingCycles |*| forks) =>
              val (eaten |*| (fork1 |*| fork2)) = eatOnce(name)(forks)

              // after the philosopher has eaten, let her think for a while
              val thought = when(eaten) { think(name) }

              // Rinse and repeat.
              // Prevent the recursive call to proceed concurrently to thinking by
              // delaying the remaining cycles value until thinking has finished.
              run((fork1 |*| fork2) |*| (remainingCycles waitFor thought))
            }
        )
      }
    }

  private def think(name: String): Done -⚬ Done =
    printLine(s"😴 $name falling asleep") > randomDelay > printLine(s"🔔 $name wakes up")

  private def eatOnce(name: String): (SharedFork |*| SharedFork) -⚬ (Done |*| (SharedFork |*| SharedFork)) =
    rec { eatOnce =>
      tryEat(name) >
      |+|.signalR > // adds a `Done` signal to the right (i.e. the unsuccessful) branch
      either(
        caseLeft =
          // succeeded in picking up both forks and eating
          id[Done |*| (SharedFork |*| SharedFork)],
        caseRight =
          // failed to pick up the forks; think for a bit and then try again
          λ { case (failed |*| (lFork |*| rFork)) =>
            val (thought |*| thoughtPing) = when(failed) { think(name) > notifyDoneR }
            val (lPing |*| rPing) = thoughtPing > split
            val (eaten |*| forks) =
              eatOnce((lFork blockUntil lPing) |*| (rFork blockUntil rPing))
            join(thought |*| eaten) |*| forks
          }
      )
    }

  /** Attempts to pick up both forks and eat.
    * Whether it succeeds or not, puts the forks back on the table.
    * Results in left if managed to eat, right if not (failed to pick up one of the forks).
    */
  private def tryEat(name: String):
    (SharedFork |*| SharedFork) -⚬ (
      // returned when managed to pick up both forks and eat. The `Done` signal signals when eating is finished
      (Done |*| (SharedFork |*| SharedFork)) |+|
      // returned when failed to pick up one of the forks
      (SharedFork |*| SharedFork)
    ) =
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
                  eat(name)(lHeldFork |*| rHeldFork) >
                    λ { case (eaten |*| (lhf |*| rhf)) =>
                      injectL(eaten |*| (putDown(lhf) |*| putDown(rhf)))
                    }
                },
              caseRight =
                // failed to pick up the right fork
                λ { case (lHeldFork |*| rFork) =>
                  // put down the left fork and return failure (via `injectR`)
                  injectR(putDown(lHeldFork) |*| rFork)
                },
            )
          },
        caseRight =
          // failed to pick up the left fork
          λ { case (lFork |*| rFork) =>
            // return failure (via `injectR`)
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
