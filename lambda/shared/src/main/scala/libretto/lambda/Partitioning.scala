package libretto.lambda

import libretto.lambda.util.{Applicative, TypeEqK}

trait Partitioning[->[_, _], <+>[_, _], T] {
  type Partition[P]

  def union[P, Q](p: Partition[P], q: Partition[Q]): Partition[P <+> Q]

  def compileAt[<*>[_, _], F[_], G[_], R](
    pos: Focus[<*>, F],
    handle: [X] => Partition[X] => G[F[X] -> R],
  )(using
    Applicative[G],
  ): G[F[T] -> R]

  def isTotal[P](p: Partition[P]): Option[T -> P]

  def sameAs(that: Partitioning[->, <+>, T]): Option[TypeEqK[this.Partition, that.Partition]]
}

object Partitioning {

  class Partition[->[_, _], <+>[_, _], T, P](
    val partitioning: Partitioning[->, <+>, T],
    val partition:    partitioning.Partition[P],
  ) {
    def isTotal: Option[T -> P] =
      partitioning.isTotal(partition)
  }

}
