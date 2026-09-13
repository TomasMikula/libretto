package libretto.lambda.util

trait Functional[F[_, _]] {
  def uniqueOutputType[A, B, C](f: F[A, B], g: F[A, C]): B =:= C
}

trait Functional2[F[_, _, _]] {
  def uniqueOutputType[A, B, R, S](r: F[A, B, R], s: F[A, B, S]): R =:= S

  extension [A, B, R](r: F[A, B, R]) {
    infix def uniq[S](s: F[A, B, S]): R =:= S =
      uniqueOutputType(r, s)
  }
}
