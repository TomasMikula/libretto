package libretto.lambda

trait Unzippable[|*|[_, _], F[_]] {
  def unzip[A, B](fab: F[A |*| B]): (F[A], F[B])

  object Unzip {
    def unapply[A, B](fab: F[A |*| B]): (F[A], F[B]) =
      unzip(fab)
  }
}
