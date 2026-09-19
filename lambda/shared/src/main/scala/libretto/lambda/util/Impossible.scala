package libretto.lambda.util

trait Impossible3[F[_, _, _]] {
  def contradiction[A, B, C](x: F[A, B, C]): Nothing

  extension [A, B, C](x: F[A, B, C]) {
    def absurd: Nothing = contradiction(x)
  }
}

object Impossible3 {
  def apply[F[_, _, _]](prove: [x, y, z] => F[x, y, z] => Nothing): Impossible3[F] =
    new Impossible3[F]:
      override def contradiction[A, B, C](x: F[A, B, C]): Nothing = prove(x)
}
