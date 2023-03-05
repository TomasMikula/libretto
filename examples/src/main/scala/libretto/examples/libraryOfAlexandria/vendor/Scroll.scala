package libretto.examples.libraryOfAlexandria.vendor

private[vendor] case class Scroll(text: String) {

  def paginate(): Iterator[(Int, String)] =
    text
      .grouped(120)
      .map(_.grouped(40).mkString("    ", "\n    ", ""))
      .zipWithIndex
      .map { case (content, i) => (i+1, content) }

}
