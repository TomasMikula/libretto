package libretto.typology.toylang.types

final case class Label(value: Int)

object Label {
  given Ordering[Label] with {
    override def compare(
      x: Label,
      y: Label,
    ): Int =
      (x, y) match
        case (Label(x), Label(y)) => x.compareTo(y)
  }
}
