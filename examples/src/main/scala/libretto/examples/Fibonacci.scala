package libretto.examples

import libretto.StarterApp

object Fibonacci extends StarterApp {

  override def blueprint: Done -⚬ Done =
    printLine("Press Enter to get the next Fibonacci number, type anything else to quit.")
      .>(fork)
      .>(snd(fibonacci))
      .>(assocRL)
      .>(fst(go))
      .>(join)

  private def go: (Done |*| Endless[Val[Long]]) -⚬ Done = rec { go =>
    val next: (Done |*| Endless[Val[Long]]) -⚬ Done =
      snd(Endless.pull > fst(mapVal[Long, String](_.toString) > printLine)) > assocRL > fst(join) > go

    val quit: (Done |*| Endless[Val[Long]]) -⚬ Done =
      elimSnd(Endless.close)

    fst(readLine > mapVal(_ == "") > liftBoolean) > Bool.switchWithR(
      caseTrue = next,
      caseFalse = quit,
    )
  }

  private def fibonacci: Done -⚬ (Endless[Val[Long]] |*| Done) = {
    val step: Val[(Long, Long)] -⚬ (Val[Long] |*| Val[(Long, Long)]) =
      id[Val[(Long, Long)]] > mapVal { case (n0, n1) => (n0, (n1, n0 + n1)) } > liftPair

    constVal((0L, 1L)) > Endless.unfold(step) > snd(neglect)
  }
}
