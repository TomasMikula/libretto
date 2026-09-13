package libretto.lambda.util

trait Functional[F[_, _]] {
  def uniqueOutputType[A, B, C](f: F[A, B], g: F[A, C]): B =:= C
}

trait Functional2[F[_, _, _]] {
  def uniqueOutputType[A, B, R, S](r: F[A, B, R], s: F[A, B, S]): R =:= S
}
