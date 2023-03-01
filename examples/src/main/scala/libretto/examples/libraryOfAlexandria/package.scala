package libretto.examples

package object libraryOfAlexandria {
  case class ScrollId(value: String)
  case class Page(scrollId: ScrollId, pageNumber: Int, content: String)
}
