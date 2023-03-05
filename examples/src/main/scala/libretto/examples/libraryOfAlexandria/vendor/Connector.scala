package libretto.examples.libraryOfAlexandria.vendor

object Connector {
  def newInstance(): Connector =
    new ConnectorImpl()
}

trait Connector {
  def connect(): Connection
  def close(): Unit
}
