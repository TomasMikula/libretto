package libretto.lambda

import libretto.lambda.util.{Applicative, TypeEqK}

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

  def identity[->[_, _], <*>[_, _], T](using Category[->]): Extractor[->, <*>, T, T] =
    Extractor(IdPartitioning[->, <*>, T](), summon[T =:= T])

  private class IdPartitioning[->[_, _], <*>[_, _], T](using cat: Category[->]) extends Partitioning[->, <*>, T] {

    override type Partition[P] = T =:= P

    override def reinject[P](p: T =:= P): P -> T =
      cat.id[P].to[T](using p.flip)

    override def sameAs(that: Partitioning[->, <*>, T]): Option[TypeEqK[this.Partition, that.Partition]] =
      that match
        case that1: (IdPartitioning[arr, pr, t] & that.type) =>
          Some(TypeEqK.refl[this.Partition]): Option[TypeEqK[this.Partition, that1.Partition]]
        case _ =>
          None

    override def isTotal[P](p: T =:= P): Option[T -> P] =
      Some(cat.id[T].to[P](using p))

    override def samePartition[P, Q](p: T =:= P, q: T =:= Q): Option[P =:= Q] =
      Some(p.substituteCo[[X] =>> X =:= Q](q))

    override def compileAt[F[_], G[_], R](
      pos: Focus[<*>, F],
      handle: [X] => (x: T =:= X) => G[F[X] -> R]
    )(using
      Applicative[G],
    ): G[F[T] -> R] =
      handle[T](summon[T =:= T])

    override def showPartition[P](p: T =:= P): String =
      "Identity"
  }
}
