package libretto.lambda

import libretto.lambda.util.TypeEqK

trait Partitioning[->[_, _], <+>[_, _], T] {
  type Partition[P]

  def union[P, Q](p: Partition[P], q: Partition[Q]): Partition[P <+> Q]

  def isTotal[P](p: Partition[P]): Option[T -> P]

  def sameAs(that: Partitioning[->, <+>, T]): Option[TypeEqK[this.Partition, that.Partition]]
}

object Partitioning {

  class Matcher[->[_, _], <+>[_, _], T, P](
    val partitioning: Partitioning[->, <+>, T],
    val partition:    partitioning.Partition[P],
  ) {
    def isTotal: Option[T -> P] =
      partitioning.isTotal(partition)
  }

}
