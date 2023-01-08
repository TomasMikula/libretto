package libretto.util

trait Functional[F[_, _]] {
  def uniqueOutputType[A, B, C](f: F[A, B], g: F[A, C]): B =:= C
}
