package libretto.util

object unapply {
  trait Unapply[FA, F[_]] {
    type A
    def ev: FA =:= F[A]
  }

  object Unapply {
    implicit def unapplyInstance[F[_], X]: Unapply[F[X], F] { type A = X } =
      new Unapply[F[X], F] {
        type A = X
        val ev: F[X] =:= F[A] = implicitly
      }
  }

  trait Unapply2[FAB, F[_, _]] {
    type A
    type B
    def ev: FAB =:= F[A, B]
  }

  object Unapply2 {
    implicit def unapply2Instance[F[_, _], X, Y]: Unapply2[F[X, Y], F] { type A = X; type B = Y } =
      new Unapply2[F[X, Y], F] {
        type A = X
        type B = Y
        val ev: F[X, Y] =:= F[A, B] = implicitly
      }
  }
}
