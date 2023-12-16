package libretto.typology.toylang.types

enum Label {
  case Abstr(value: AbstractTypeLabel)
  case ScalaTParam(value: ScalaTypeParam)
}

object Label {
  given Ordering[Label] with {
    private val ScalaTypeParamOrdering =
      Ordering.Tuple3[String, Int, String]

    override def compare(
      x: Label,
      y: Label,
    ): Int =
      (x, y) match
        case (ScalaTParam(ScalaTypeParam(f1, l1, n1)), ScalaTParam(ScalaTypeParam(f2, l2, n2))) =>
          ScalaTypeParamOrdering.compare((f1, l1, n1), (f2, l2, n2))
        case (ScalaTParam(_), Abstr(_)) => -1
        case (Abstr(_), ScalaTParam(_)) => 1
        case (Abstr(AbstractTypeLabel(x)), Abstr(AbstractTypeLabel(y))) => x compareTo y
  }
}
