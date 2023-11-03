package libretto.lambda.util

trait Injective[F[_]] {
  def unapply[A, B](ev: F[A] =:= F[B]): Tuple1[A =:= B]
}

object Injective {
  def apply[F[_]](using Injective[F]): Injective[F] =
    summon[Injective[F]]

  given id: Injective[[x] =>> x] with
    override def unapply[A, B](ev: A =:= B): Tuple1[A =:= B] =
      Tuple1(ev)
}
