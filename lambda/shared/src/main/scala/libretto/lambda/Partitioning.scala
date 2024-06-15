package libretto.lambda

import libretto.lambda.util.{Applicative, TypeEq, TypeEqK}
import libretto.lambda.util.TypeEq.Refl

trait Partitioning[->[_, _], <*>[_, _], T] { self =>
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

  def showPartition[P](p: Partition[P]): String

  def contramap[Fun[_, _], S](
    f: Fun[S, T],
  )(using
    Partitioning.SubFun[->, Fun],
    SemigroupalCategory[->, <*>],
  ): Partitioning[->, <*>, S] { type Partition[P] = self.Partition[P] } =
    Partitioning.Contramapped(this, f)
}

object Partitioning {

  trait SubFun[->[_, _], F[_, _]] {
    infix def sameAs[G[_, _]](that: SubFun[->, G]): Option[[X, Y] => F[X, Y] => G[X, Y]]
    def testEqual[X, Y, Z](f: F[X, Y], g: F[X, Z]): Option[Y =:= Z]
    def compile[X, Y](f: F[X, Y]): (X -> Y)
    def reverseCompile[X, Y](f: F[X, Y]): (Y -> X)
  }
  private class Contramapped[->[_, _], <*>[_, _], T, Fun[_, _], S, Pt[_]](
    private val base: Partitioning[->, <*>, T] { type Partition[P] = Pt[P] },
    private val pre: Fun[S, T],
  )(using
    private val sf: SubFun[->, Fun],
    sc: SemigroupalCategory[->, <*>],
  ) extends Partitioning[->, <*>, S] {
    final type Partition[P] = Pt[P]

    override def isTotal[P](p: Partition[P]): Option[S -> P] =
      base.isTotal(p).map(f => sf.compile(pre) > f)

    override def reinject[P](p: Partition[P]): P -> S =
      base.reinject(p) > sf.reverseCompile(pre)

    override def showPartition[P](p: Partition[P]): String =
      base.showPartition(p)

    override def samePartition[P, Q](p: Partition[P], q: Partition[Q]): Option[P =:= Q] =
      base.samePartition(p, q)

    override def sameAs(that: Partitioning[->, <*>, S]): Option[TypeEqK[Pt, that.Partition]] =
      that match
        case that1: (Contramapped[arr, pr, u, f, s, pt] & that.type) =>
          sameAsContramapped[u, f, that1.Partition](that1)
        case _ =>
          None

    private def sameAsContramapped[U, G[_, _], Qt[_]](that: Contramapped[->, <*>, U, G, S, Qt]): Option[TypeEqK[Pt, Qt]] =
      (that.sf sameAs this.sf)
        .flatMap { ev =>
          val pre1: Fun[S, U] = ev(that.pre)
          sf.testEqual(pre, pre1)
            .flatMap { case TypeEq(Refl()) =>
              this.base sameAs that.base
            }
        }

    override def compileAt[F[_], G[_], R](
      pos: Focus[<*>, F],
      handle: [X] => Pt[X] => G[F[X] -> R],
    )(using
      Applicative[G],
    ): G[F[S] -> R] =
      base
        .compileAt(pos, handle)
        .map(f => sf.compile(pre).at(pos) > f)
  }
}
