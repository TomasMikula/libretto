package libretto.examples.diningPhilosophers

import libretto.StarterApp

object DiningPhilosophers extends StarterApp {
  import $._

  val philosophers = Philosophers(ForksProvider)
  import philosophers.{behavior => philosopher}
  import ForksProvider.mkSharedFork

  override def blueprint: Done -⚬ Done =
    λ { start =>
      // make 5 forks, with two accessor interfaces each
      val ((f1l |*| f1r) |*| ((f2l |*| f2r) |*| ((f3l |*| f3r) |*| ((f4l |*| f4r) |*| (f5l |*| f5r))))) =
        when(start) {
          mkSharedFork /\ (mkSharedFork /\ (mkSharedFork /\ (mkSharedFork /\ mkSharedFork)))
        }

      // start 5 philosophers, giving each one access to two different forks
      val philosopherProcesses: $[LList1[Done]] =
        LList1(
          philosopher("Aristotle")(cycles = 5)(f1r |*| f2l),
          philosopher("Bolzano"  )(cycles = 5)(f2r |*| f3l),
          philosopher("Confucius")(cycles = 5)(f3r |*| f4l),
          philosopher("Descartes")(cycles = 5)(f4r |*| f5l),
          philosopher("Epictetus")(cycles = 5)(f5r |*| f1l),
        )

      // wait for all philosophers to complete
      philosopherProcesses > LList1.fold
    }
}
