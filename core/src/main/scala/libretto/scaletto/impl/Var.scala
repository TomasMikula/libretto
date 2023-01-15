package libretto.scaletto.impl

import libretto.lambda.Variable
import libretto.util.TypeEq
import libretto.util.TypeEq.Refl

/**
 * @param P representation of variable's origin (e.g. source code position)
 */
class Var[P, A](val origin: P) {
  def testEqual[B](that: Var[P, B]): Option[A =:= B] =
    if (this eq that) Some(summon[A =:= A].asInstanceOf[A =:= B])
    else None
}

object Var {
  given [P]: Variable[Var[P, *], Set[Var[P, ?]]] =
    new Variable[Var[P, *], Set[Var[P, ?]]] {
      override def testEqual[A, B](a: Var[P, A], b: Var[P, B]): Option[A =:= B] =
        a testEqual b

      override def unapply[A, B](ev: Var[P, A] =:= Var[P, B]): Tuple1[A =:= B] =
        ev match { case TypeEq(Refl()) => Tuple1(summon[A =:= B]) }

      override def singleton[A](v: Var[P, A]): Set[Var[P, ?]] =
        Set(v)

      override def union(vs: Set[Var[P, ?]], ws: Set[Var[P, ?]]): Set[Var[P, ?]] =
        vs union ws
    }
}
