package libretto.lambda

import libretto.lambda.util.{Applicative, TypeEqK}

trait Partitioning[->[_, _], <*>[_, _], T] {
  type Partition[P]

  def compileAt[F[_], G[_], R](
    pos: Focus[<*>, F],
    handle: [X] => Partition[X] => G[F[X] -> R],
  )(using
    Applicative[G],
  ): G[F[T] -> R]

  def isTotal[P](p: Partition[P]): Option[T -> P]

  infix def sameAs(that: Partitioning[->, <*>, T]): Option[TypeEqK[this.Partition, that.Partition]]

  def samePartition[P, Q](p: Partition[P], q: Partition[Q]): Option[P =:= Q]

  def reinject[P](p: Partition[P]): P -> T

  def extractor[P](p: Partition[P]): Partitioning.Extractor[->, <*>, T, P] =
    Partitioning.Extractor(this, p)
}

object Partitioning {

  class Extractor[->[_, _], <*>[_, _], T, P](
    val partitioning: Partitioning[->, <*>, T],
    val partition:    partitioning.Partition[P],
  ) {
    def isTotal: Option[T -> P] =
      partitioning.isTotal(partition)

    def reinject: P -> T =
      partitioning.reinject(partition)

    infix def sameAs[Q](that: Extractor[->, <*>, T, Q]): Option[Option[P =:= Q]] =
      (this.partitioning sameAs that.partitioning)
        .map { ev =>
          this.partitioning.samePartition(this.partition, ev.flip.at[Q](that.partition))
        }
  }

  sealed trait RebaseRes[->[_, _], <*>[_, _], T, Q, P]
  object RebaseRes {
    case class Incompatible[->[_, _], <*>[_, _], T, Q, P]() extends RebaseRes[->, <*>, T, Q, P]
  }
}
