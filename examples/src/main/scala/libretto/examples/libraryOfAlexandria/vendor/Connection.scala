package libretto.examples.libraryOfAlexandria.vendor

trait Connection {
  def fetchScroll(id: ScrollId): Option[ResultSet[Page]]
  def close(): Unit
}
