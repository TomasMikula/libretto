package libretto.examples.libraryOfAlexandria.vendor

trait ResultSet[T] {
  def next(): Option[T]
  def earlyClose(): Unit
}
