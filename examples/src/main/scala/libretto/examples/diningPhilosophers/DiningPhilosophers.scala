package libretto.examples.diningPhilosophers

import libretto.scaletto.StarterApp

object DiningPhilosophers extends StarterApp {
  import $._

  val philosophers = Philosophers(ForksProvider)
  import philosophers.{behavior => philosopher}
  import ForksProvider.mkSharedFork

  override def blueprint: Done -⚬ Done =
    λ { (start: $[Done]) =>
      // make 5 forks, with two accessor interfaces each
      val ((f1l |*| f1r) |*| ((f2l |*| f2r) |*| ((f3l |*| f3r) |*| ((f4l |*| f4r) |*| (f5l |*| f5r))))) =
        when(start) {
          // the `f /\ g` operator splits the incoming `Done` signal into two
          // and applies `f` to the left one and `g` to the right one
          mkSharedFork /\ (mkSharedFork /\ (mkSharedFork /\ (mkSharedFork /\ mkSharedFork)))
        }

      // Start 5 philosophers, giving each one access to two different forks.
      // Each philosopher outputs a `Done` signal when finished.
      // (`LList1` is a non-empty list of linear resources.)
      val philosopherProcesses: $[LList1[Done]] =
        LList1(
          philosopher("Aristotle")(cycles = 5)(f1r |*| f2l),
          philosopher("Bolzano"  )(cycles = 5)(f2r |*| f3l),
          philosopher("Confucius")(cycles = 5)(f3r |*| f4l),
          philosopher("Descartes")(cycles = 5)(f4r |*| f5l),
          philosopher("Epictetus")(cycles = 5)(f5r |*| f1l),
        )

      // Wait for all philosophers to complete.
      // (`Done` signal forms a semigroup (via `join`-ing the signals) and thus
      // a non-empty list of them can be folded into a single `Done` signal.)
      philosopherProcesses > LList1.fold
    }
}
