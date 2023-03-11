package libretto.examples.tv

import libretto.scaletto.StarterApp

object Main extends StarterApp {
  override def blueprint: Done -⚬ Done =
    TvBroadcaster.blueprint > TvViewer.blueprint
}
