package libretto.typology.toylang.types

enum Label {
  case Abstr(value: AbstractTypeLabel)
}

object Label {
  given Ordering[Label] with {
    override def compare(
      x: Label,
      y: Label,
    ): Int =
      (x, y) match
        case (Abstr(AbstractTypeLabel(x)), Abstr(AbstractTypeLabel(y))) => x.compareTo(y)
  }
}
