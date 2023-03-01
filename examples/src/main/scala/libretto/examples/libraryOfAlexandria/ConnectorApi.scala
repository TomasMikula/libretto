package libretto.examples.libraryOfAlexandria

import libretto.scaletto.StarterKit._
import libretto.stream.scaletto.DefaultStreams._

trait ConnectorApi {
  type Connector
  def fetch: (Connector |*| Val[ScrollId]) -⚬ ValSource[Page]
}
