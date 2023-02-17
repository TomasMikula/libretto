package libretto.lambda

import libretto.lambda.util.Zippable

trait Cartesian[|*|[_, _], F[_]] extends Zippable[|*|, F] {
  def unzip[A, B](fab: F[A |*| B]): (F[A], F[B])

  object Unzip {
    def unapply[A, B](fab: F[A |*| B]): (F[A], F[B]) =
      unzip(fab)
  }
}
