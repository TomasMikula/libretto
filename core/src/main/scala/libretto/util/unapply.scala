package libretto.util

object unapply {
  trait Unapply[FA, F[_]] {
    type A
    def ev: FA =:= F[A]
  }

  object Unapply {
    given [F[_], X]: Unapply[F[X], F] with {
      type A = X
      val ev: F[X] =:= F[A] = summon
    }
  }

  trait Unapply2[FAB, F[_, _]] {
    type A
    type B
    def ev: FAB =:= F[A, B]
  }

  object Unapply2 {
    given [F[_, _], X, Y]: Unapply2[F[X, Y], F] with {
      type A = X
      type B = Y
      val ev: F[X, Y] =:= F[A, B] = summon
    }
  }
}
