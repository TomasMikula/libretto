package libretto.examples.libraryOfAlexandria

import libretto.scaletto.StarterKit.*
import libretto.stream.scaletto.DefaultStreams.*

import vendor.{Page, ScrollId}

trait ConnectorModule {
  type Connector

  given shareableConnector: CloseableCosemigroup[Connector]

  def closeConnector: Connector -⚬ Done

  def fetchScroll: (Connector |*| Val[ScrollId]) -⚬ ValSource[Page]
}
