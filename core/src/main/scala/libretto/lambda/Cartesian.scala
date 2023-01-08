package libretto.lambda

import libretto.util.Zippable

trait Cartesian[|*|[_, _], F[_]] extends Zippable[|*|, F] {
  def unzip[A, B](fab: F[A |*| B]): (F[A], F[B])
}
