package libretto.typology.kinds

/** Evidence that `K` is a kind, i.e. a legal output "type" of type functions (incl. nullary). */
sealed trait Kind[K] {
  def isNotPair: [x, y] => (K =:= (x × y)) => Nothing =
    [x, y] => (ev: K =:= (x × y)) =>
      Kind.cannotBePair(ev.substituteCo(Kind.this))

  override def toString: String =
    this match
      case Kind.Type => "●"
}

object Kind {
  case object Type extends Kind[●]

  given Kind[●] = Type

  def apply[K](using Kind[K]): Kind[K] =
    summon[Kind[K]]

  def cannotBePair[K, L](ab: Kind[K × L]): Nothing =
    throw AssertionError("Impossible")
}
