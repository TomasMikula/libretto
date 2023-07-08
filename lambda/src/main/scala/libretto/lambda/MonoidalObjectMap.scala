package libretto.lambda

trait MonoidalObjectMap[F[_, _], |*|[_, _], One, <*>[_, _], Unit] extends SemigroupalObjectMap[|*|, <*>, F] {
  def unit: F[One, Unit]
}