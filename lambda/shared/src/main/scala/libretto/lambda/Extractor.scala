package libretto.lambda

trait Extractor[->[_, _], <*>[_, _], T, P] {
  val partitioning: Partitioning[->, <*>, T]
  val partition:    partitioning.Partition[P]

  def isTotal: Option[T -> P] =
    partitioning.isTotal(partition)

  def reinject: P -> T =
    partitioning.reinject(partition)

  infix def sameAs[Q](that: Extractor[->, <*>, T, Q]): Option[Option[P =:= Q]] =
    (this.partitioning sameAs that.partitioning)
      .map { ev =>
        this.partitioning.samePartition(this.partition, ev.flip.at[Q](that.partition))
      }

  def show: String =
    partitioning.showPartition(partition)

  def contramap[Fun[_, _], S](f: Fun[S, T])(using
    Partitioning.SubFun[->, Fun],
    SemigroupalCategory[->, <*>],
  ): Extractor[->, <*>, S, P] =
    val pg = partitioning.contramap(f)
    Extractor(pg, partition)
}

object Extractor {
  def apply[->[_, _], <*>[_, _], T, P](
    partitioning: Partitioning[->, <*>, T],
    partition:    partitioning.Partition[P],
  ): Extractor[->, <*>, T, P] =
    Impl[->, <*>, T, P](partitioning, partition)

  trait Via[->[_, _], <*>[_, _], T, P](
    val delegate: Extractor[->, <*>, T, P],
  ) extends Extractor[->, <*>, T, P] {
    override val partitioning: delegate.partitioning.type  = delegate.partitioning
    override val partition:    partitioning.Partition[P]   = delegate.partition
  }

  private class Impl[->[_, _], <*>[_, _], T, P](
    override val partitioning: Partitioning[->, <*>, T],
    override val partition:    partitioning.Partition[P],
  ) extends Extractor[->, <*>, T, P]
}
