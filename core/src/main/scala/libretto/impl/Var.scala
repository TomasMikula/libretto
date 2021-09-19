package libretto.impl

class Var[A]() {
  def testEqual[B](that: Var[B]): Option[A =:= B] =
    if (this eq that) Some(summon[A =:= A].asInstanceOf[A =:= B])
    else None
}

object Var {
  given Variable[Var, Set[Var[?]]] =
    new Variable[Var, Set[Var[?]]] {
      override def testEqual[A, B](a: Var[A], b: Var[B]): Option[A =:= B] =
        a testEqual b

      override def singleton[A](v: Var[A]): Set[Var[?]] =
        Set(v)

      override def union(vs: Set[Var[?]], ws: Set[Var[?]]): Set[Var[?]] =
        vs union ws
    }
}
