package libretto.examples.libraryOfAlexandria

import libretto.scaletto.StarterKit._
import libretto.stream.scaletto.DefaultStreams._

import vendor.{Page, ScrollId}

object Downloader {
  def apply(cm: ConnectorModule): Downloader[cm.type] =
    new Downloader(cm)
}

class Downloader[CM <: ConnectorModule](val cm: CM) {
  def downloadAll(prepareAhead: Int): (cm.Connector |*| ValSource[ScrollId]) -⚬ ValSource[Page] =
    fetchForEach
     > Source.prefetch(prepareAhead)(discardPrefetched = ValSource.close)
     > Source.flatten

  private def fetchForEach: (cm.Connector |*| ValSource[ScrollId]) -⚬ Source[ValSource[Page]] =
    Source.mapWith(cm.fetchScroll)
}
