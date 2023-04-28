package libretto.typology.util

import libretto.lambda.util.Monad

opaque type State[S, A] = S => (S, A)

object State {
  def apply[S, A](f: S => (S, A)): State[S, A] =
    f

  extension [S, A](fa: State[S, A]) {
    def run(s: S): A =
      fa(s)._2
  }

  given monadState[S]: Monad[State[S, *]] with {
    override def pure[A](a: A): State[S, A] =
      s => (s, a)

    override def flatMap[A, B](fa: State[S, A])(f: A => State[S, B]): State[S, B] =
      s => {
        val (s1, a) = fa(s)
        f(a)(s1)
      }
  }
}
