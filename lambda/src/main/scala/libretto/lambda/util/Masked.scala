package libretto.lambda.util

sealed trait Masked[F[_], A] {
  type X
  val value: F[X]
  def ev: X =:= A

  def visit[R](f: [T] => (F[T], T =:= A) => R): R =
    f[X](value, ev)
}

object Masked {
  def apply[F[_], A](fa: F[A]): Masked[F, A] =
    new Masked[F, A] {
      override type X = A
      override val value: F[X] = fa
      override def ev: A =:= A = summon
    }
}
