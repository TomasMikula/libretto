package libretto.lambda

import libretto.lambda.util.{Exists, Injective, TypeEq, UniqueTypeArg}
import libretto.lambda.util.TypeEq.Refl
import scala.collection.{immutable as sci}

/**
 * @param P representation of variable's origin (e.g. source code position)
 */
class Var[P, A] private[lambda](
  val origin: P,
  val context: AnyRef, // XXX
) {
  infix def testEqual[B](that: Var[P, B]): Option[A =:= B] =
    if (this eq that) Some(summon[A =:= A].asInstanceOf[A =:= B])
    else None

  override def toString: String =
    s"${super.toString} ($origin)"
}

object Var {
  opaque type Set[P] = sci.Set[Var[P, ?]]
  object Set {
    def apply[P](vs: Var[P, ?]*): Set[P] =
      sci.Set.from(vs)

    def fromList[P](vs: List[Var[P, ?]]): Set[P] =
      sci.Set.from(vs)

    extension [P](vs: Var.Set[P]) {
      infix def merge(ws: Var.Set[P]): Var.Set[P] =
        sci.Set.concat(vs, ws)

      def list: List[Var[P, ?]] =
        List.from(vs)

      infix def containsVar[A](v: Var[P, A]): Boolean =
        (vs: sci.Set[Var[P, ?]]) contains v

      def +[A](v: Var[P, A]): Var.Set[P] =
        (vs: sci.Set[Var[P, ?]]) + v
    }
  }

  /** A map of type-aligned entries `Var[V, A] -> F[A]`. */
  opaque type Map[V, F[_]] = sci.Map[Var[V, Any], F[Any]]
  object Map {
    def empty[V, F[_]]: Var.Map[V, F] = sci.Map.empty

    extension [V, F[_]](m: Var.Map[V, F]) {
      private def reveal: sci.Map[Var[V, Any], F[Any]] =
        m

      def --(keys: Var.Set[V]): Var.Map[V, F] =
        m.reveal.removedAll((keys: sci.Set[Var[V, ?]]).asInstanceOf[sci.Set[Var[V, Any]]])

      def +[A](kv: (Var[V, A], F[A])): Var.Map[V, F] =
        val k: Var[V, Any] = kv._1.asInstanceOf
        val v: F[Any]      = kv._2.asInstanceOf
        m.reveal.updated(k, v)

      def foldLeft[Z](init: Z)(f: [A] => (Z, Var[V, A], F[A]) => Z): Z =
        m.reveal.foldLeft(init) { (z, kv) =>
          f[Any](z, kv._1, kv._2)
        }

      def values: List[Exists[F]] =
        m.reveal.valuesIterator.map(f => Exists(f)).toList

      def toList[T](f: [x] => (Var[V, x], F[x]) => T): List[T] =
        m.reveal.iterator.map { case (k, v) => f(k, v) }.toList
    }
  }

  given [P]: Injective[Var[P, _]] with {
    override def unapply[A, B](ev: Var[P, A] =:= Var[P, B]): Tuple1[A =:= B] =
      ev match { case TypeEq(Refl()) => Tuple1(summon[A =:= B]) }
  }

  given [P]: UniqueTypeArg[Var[P, _]] with {
    override def testEqual[A, B](a: Var[P, A], b: Var[P, B]): Option[A =:= B] =
      a testEqual b
  }
}
