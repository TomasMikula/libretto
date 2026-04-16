package kindville

private[kindville] opaque type Groups[A] =
  List[SingleOrMultiple[A]]

private[kindville] object Groups {

  def fromList[A](as: List[SingleOrMultiple[A]]): Groups[A] =
    as

  extension [A](as: Groups[A]) {
    def totalSize: Int =
      as.map(_.size).sum

    def toList: List[SingleOrMultiple[A]] =
      as

    def toFlatList: List[A] =
      as.flatMap(_.toList)

    def map[B](f: A => B): Groups[B] =
      as.map(_.map(f))

    def mapGroups[B](f: SingleOrMultiple[A] => B): List[B] =
      as.map(f)

    def zipWithListUnsafe[B](
      bs: List[B],
    ): Groups[(A, B)] = {
      val n = as.totalSize
      require(bs.size == n, s"List of size $n required, got a list of size ${bs.size}")

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
  }

}