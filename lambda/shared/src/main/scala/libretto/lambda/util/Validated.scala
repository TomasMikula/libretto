package libretto.lambda.util

enum Validated[+E, A] {
  case Valid(value: A)
  case Invalid(errors: NonEmptyList[E])

  def map[B](f: A => B): Validated[E, B] =
    this match
      case Valid(a)    => Valid(f(a))
      case Invalid(es) => Invalid(es)

  def emap[F](f: E => F): Validated[F, A] =
    this match
      case Valid(a)    => Valid(a)
      case Invalid(es) => Invalid(es.map(f))

  infix def zip[E1 >: E, B](that: Validated[E1, B]): Validated[E1, (A, B)] =
    (this, that) match
      case (Valid(a)   , Valid(b)   ) => Valid((a, b))
      case (Valid(_)   , Invalid(fs)) => Invalid(fs)
      case (Invalid(es), Valid(_)   ) => Invalid(es)
      case (Invalid(es), Invalid(fs)) => Invalid(es ++ fs)

  def flatMap[E1 >: E, B](f: A => Validated[E1, B]): Validated[E1, B] =
    this match
      case Valid(a)   => f(a)
      case Invalid(e) => Invalid(e)

  def valueOr[AA >: A](f: NonEmptyList[E] => AA): AA =
    this match
      case Valid(a) => a
      case Invalid(es) => f(es)

  def recoverWith[F, AA >: A](f: NonEmptyList[E] => Validated[F, AA]): Validated[F, AA] =
    this match
      case Valid(a) => Valid(a)
      case Invalid(es) => f(es)
}

object Validated {
  def invalid[E, A](e: E): Validated[E, A] =
    Invalid(NonEmptyList(e, Nil))

  def valid[E, A](a: A): Validated[E, A] =
    Valid(a)

  def fromEither[E, A](x: Either[E, A]): Validated[E, A] =
    x match
      case Right(a) => Valid(a)
      case Left(e) => invalid(e)

  given applicative[E]: Applicative[Validated[E, _]] with {
    override def pure[A](a: A): Validated[E, A] = Valid(a)

    extension [A](fa: Validated[E, A]) {
      override def map[B](f: A => B): Validated[E, B] = fa.map(f)
      override def zip[B](fb: Validated[E, B]): Validated[E, (A, B)] = fa zip fb

    }
  }

  given monad[E]: Monad[Validated[E, _]] with {
    extension [A](fa: Validated[E, A])
      override def flatMap[B](f: A => Validated[E, B]): Validated[E, B] =
        fa.flatMap(f)

    override def pure[A](a: A): Validated[E, A] =
      Valid(a)
  }
}
