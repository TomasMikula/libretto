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

  def zipWithListUnsafe[B](bs: List[B]): (SingleOrMultiple[(A, B)], List[B]) =
    this match
      case Single(a) =>
        bs match
          case Nil => throw new IllegalArgumentException(s"Cannot zip $this with an empty list")
          case h :: t => (Single((a, h)), t)
      case Multiple(as) =>
        val na = as.size
        val nb = bs.size
        if (nb < na)
          throw new IllegalArgumentException(s"A list with at least $na elements required, but got a list with only $nb elements")
        else
          val (bs1, bs2) = bs.splitAt(na)
          (Multiple(as zip bs1), bs2)
}

private[kindville] object SingleOrMultiple {
  def zipManyWithListUnsafe[A, B](
    as: List[SingleOrMultiple[A]],
    bs: List[B],
  ): List[SingleOrMultiple[(A, B)]] =
    val n = as.map(_.size).sum
    if (bs.size != n)
      throw new IllegalArgumentException(s"Size of the second argument (${bs.size}) does not match the first one ($n)")
    def go(as: List[SingleOrMultiple[A]], bs: List[B]): List[SingleOrMultiple[(A, B)]] =
      as match
        case h :: t =>
          val (ab, bs1) = h.zipWithListUnsafe(bs)
          ab :: go(t, bs1)
        case Nil =>
          assert(bs.isEmpty)
          Nil
    go(as, bs)
}
