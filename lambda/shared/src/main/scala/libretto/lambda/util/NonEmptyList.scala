package libretto.lambda.util

case class NonEmptyList[A](head: A, tail: List[A]) {
  def ::(a0: A): NonEmptyList[A] =
    NonEmptyList(a0, head :: tail)

  def ++(that: NonEmptyList[A]): NonEmptyList[A] =
    NonEmptyList(head, tail ::: that.toList)

  def toList: List[A] =
    head :: tail

  def map[B](f: A => B): NonEmptyList[B] =
    NonEmptyList(f(head), tail.map(f))

  def traverse[F[_], B](f: A => F[B])(using F: Applicative[F]): F[NonEmptyList[B]] =
    F.map2(f(head), Applicative.traverseList(tail)(f))(NonEmptyList(_, _))
}
