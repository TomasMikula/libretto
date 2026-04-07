package kindville

private[kindville] enum SingleOrMultiple[A] {
  case Single(value: A)
  case Multiple(as: List[A])

  def map[B](f: A => B): SingleOrMultiple[B] =
    this match
      case Single(a) => Single(f(a))
      case Multiple(as) => Multiple(as.map(f))

  def toList: List[A] =
    this match
      case Single(a) => List(a)
      case Multiple(as) => as

  def size: Int =
    this match
      case Single(_) => 1
      case Multiple(as) => as.size
}
