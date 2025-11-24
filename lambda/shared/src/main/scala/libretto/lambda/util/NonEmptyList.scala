package libretto.lambda.util

case class NonEmptyList[+A](head: A, tail: List[A]) {
  def ::[A0 >: A](a0: A0): NonEmptyList[A0] =
    NonEmptyList(a0, head :: tail)

  def :+[A0 >: A](last: A0): NonEmptyList[A0] =
    NonEmptyList(head, tail :+ last)

  def ++[A0 >: A](that: NonEmptyList[A0]): NonEmptyList[A0] =
    NonEmptyList(head, tail ::: that.toList)

  def toList: scala.::[A] =
    scala.::(head, tail)

  def map[B](f: A => B): NonEmptyList[B] =
    NonEmptyList(f(head), tail.map(f))

  def flatMap[B](f: A => NonEmptyList[B]): NonEmptyList[B] =
    val NonEmptyList(b0, bs) = f(head)
    val cs = tail.flatMap(a => f(a).toList)
    NonEmptyList(b0, bs ::: cs)

  def traverse[F[_], B](f: A => F[B])(using F: Applicative[F]): F[NonEmptyList[B]] =
    F.map2(f(head), Applicative.traverseList(tail)(f))(NonEmptyList(_, _))

  opaque type TraverseBuilder[F[_]] = Unit

  def traverse[F[_]]: TraverseBuilder[F] =
    ()

  extension [F[_]](bf: TraverseBuilder[F])
    def apply[B](f: A => F[B])(using Applicative[F]): F[NonEmptyList[B]] =
      traverse[F, B](f)
}

object NonEmptyList {
  def of[A](head: A, tail: A*): NonEmptyList[A] =
    NonEmptyList(head, tail.toList)

  def fromList[A](as: List[A]): Option[NonEmptyList[A]] =
    as match
      case head :: tail => Some(NonEmptyList(head, tail))
      case Nil => None
}
