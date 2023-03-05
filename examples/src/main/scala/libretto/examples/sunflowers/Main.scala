package libretto.examples.sunflowers

import libretto.scaletto.StarterApp
import libretto.stream.scaletto.DefaultStreams.ValSource

object Main extends StarterApp {

  override def blueprint: Done -⚬ Done =
    λ { start =>
      val sunflowers: $[ValSource[Sunflower]] =
        start :>> ValSource.fromList(List.fill(150)(Sunflower()))
      val seedsPack |*| oilBottles =
        SunflowerProcessingFacility.blueprint(sunflowers)
      joinAll(
        seedsPack  :>> ValSource.forEachSequentially(printLine(pack   => s"Produced $pack")),
        oilBottles :>> ValSource.forEachSequentially(printLine(bottle => s"Produced $bottle")),
      )
    }

}
