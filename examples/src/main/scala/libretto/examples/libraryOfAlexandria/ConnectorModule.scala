package libretto.examples.libraryOfAlexandria

import libretto.scaletto.StarterKit._
import libretto.stream.scaletto.DefaultStreams._

import vendor.{Page, ScrollId}

trait ConnectorModule {
  type Connector
  def fetchScroll: (Connector |*| Val[ScrollId]) -⚬ ValSource[Page]
}
