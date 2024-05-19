package libretto.lambda.util

enum Validated[E, A] {
  case Valid(value: A)
  case Invalid(errors: NonEmptyList[E])

  def map[B](f: A => B): Validated[E, B] =
    this match
      case Valid(a)    => Valid(f(a))
      case Invalid(es) => Invalid(es)

  infix def zip[B](that: Validated[E, B]): Validated[E, (A, B)] =
    (this, that) match
      case (Valid(a)   , Valid(b)   ) => Valid((a, b))
      case (Valid(_)   , Invalid(fs)) => Invalid(fs)
      case (Invalid(es), Valid(_)   ) => Invalid(es)
      case (Invalid(es), Invalid(fs)) => Invalid(es ++ fs)

  def flatMap[B](f: A => Validated[E, B]): Validated[E, B] =
    this match
      case Valid(a)   => f(a)
      case Invalid(e) => Invalid(e)
}

object Validated {
  def invalid[E, A](e: E): Validated[E, A] =
    Invalid(NonEmptyList(e, Nil))

  given applicative[E]: Applicative[Validated[E, _]] with {
    override def map[A, B](fa: Validated[E, A], f: A => B): Validated[E, B] = fa.map(f)
    override def zip[A, B](fa: Validated[E, A], fb: Validated[E, B]): Validated[E, (A, B)] = fa zip fb
    override def pure[A](a: A): Validated[E, A] = Valid(a)
  }
}
