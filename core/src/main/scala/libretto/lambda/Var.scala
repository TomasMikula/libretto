package libretto.lambda

import libretto.util.{Injective, TypeEq, UniqueTypeArg}
import libretto.util.TypeEq.Refl
import scala.collection.{immutable => sci}

/**
 * @param P representation of variable's origin (e.g. source code position)
 */
class Var[P, A] private[lambda](
  val origin: P,
  val context: AnyRef, // XXX
) {
  def testEqual[B](that: Var[P, B]): Option[A =:= B] =
    if (this eq that) Some(summon[A =:= A].asInstanceOf[A =:= B])
    else None

  override def toString: String =
    s"${super.toString} ($origin)"
}

object Var {
  opaque type Set[P] = sci.Set[Var[P, ?]]
  object Set {
    def apply[P](v: Var[P, ?], vs: Var[P, ?]*): Set[P] =
      sci.Set((v +: vs): _*)

    extension [P](vs: Var.Set[P]) {
      def merge(ws: Var.Set[P]): Var.Set[P] =
        sci.Set.concat(vs, ws)

      def list: List[Var[P, ?]] =
        List.from(vs)

      def containsVar[A](v: Var[P, A]): Boolean =
        (vs: sci.Set[Var[P, ?]]) contains v

      def +[A](v: Var[P, A]): Var.Set[P] =
        (vs: sci.Set[Var[P, ?]]) + v
    }
  }

  given [P]: Injective[Var[P, *]] with {
    override def unapply[A, B](ev: Var[P, A] =:= Var[P, B]): Tuple1[A =:= B] =
      ev match { case TypeEq(Refl()) => Tuple1(summon[A =:= B]) }
  }

  given [P]: UniqueTypeArg[Var[P, *]] with {
    override def testEqual[A, B](a: Var[P, A], b: Var[P, B]): Option[A =:= B] =
      a testEqual b
  }
}
