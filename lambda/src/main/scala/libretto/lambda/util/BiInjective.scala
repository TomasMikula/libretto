package libretto.lambda.util

trait BiInjective[F[_, _]] {
  def unapply[A, B, X, Y](ev: F[A, B] =:= F[X, Y]): (A =:= X, B =:= Y)
}

object BiInjective {
  def apply[F[_, _]](using BiInjective[F]): BiInjective[F] =
    summon[BiInjective[F]]

  extension [F[_, _], A, B, X, Y](ev: F[A, B] =:= F[X, Y]) {
    def biSubst[G[_, _]](g: G[A, B])(implicit inj: BiInjective[F]): G[X, Y] = {
      val inj(ev1, ev2) = ev
      ev2.substituteCo[G[X, _]](ev1.substituteCo[G[_, B]](g))
    }
  }

  given BiInjective[Tuple2] with {
    override def unapply[A, B, X, Y](ev: (A, B) =:= (X, Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(TypeEq.Refl()) => (summon, summon) }
  }
}
