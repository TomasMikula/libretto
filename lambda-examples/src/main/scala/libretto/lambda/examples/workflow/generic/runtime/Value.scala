package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{UnhandledCase, Unzippable, Zippable}
import libretto.lambda.examples.workflow.generic.lang.{**, ++, InputPortRef, Reading}

enum Value[F[_], A]:
  case One[F[_]]() extends Value[F, Unit]

  case Pair[F[_], A1, A2](
    a1: Value[F, A1],
    a2: Value[F, A2],
  ) extends Value[F, A1 ** A2]

  case Left [F[_], A, B](a: Value[F, A]) extends Value[F, A ++ B]
  case Right[F[_], A, B](b: Value[F, B]) extends Value[F, A ++ B]

  case InPortRef[F[_], A](pa: PromiseId[A]) extends Value[F, InputPortRef[A]]
  case ReadingInput[F[_], A](pa: PromiseId[A]) extends Value[F, Reading[A]]

  /** Extension point for domain-specific values. */
  case Ext(value: F[A])

  def **[B](that: Value[F, B]): Value[F, A ** B] =
    Pair(this, that)

object Value:
  def unit[F[_]]: Value[F, Unit] =
    Value.One()

  def left[F[_], A, B](value: Value[F, A]): Value[F, A ++ B] =
    Value.Left(value)

  def right[F[_], A, B](value: Value[F, B]): Value[F, A ++ B] =
    Value.Right(value)

  def inputPortRef[F[_], A](promiseId: PromiseId[A]): Value[F, InputPortRef[A]] =
    InPortRef(promiseId)

  def reading[F[_], A](pa: PromiseId[A]): Value[F, Reading[A]] =
    ReadingInput(pa)

  def unpair[F[_], A, B](value: Value[F, A ** B])(using F: Unzippable[**, F]): (Value[F, A], Value[F, B]) =
    value match
      case Pair(a, b) =>
        (a, b)
      case Ext(value) =>
        val (a, b) = F.unzip(value)
        (Ext(a), Ext(b))

  def toEither[F[_], A, B](value: Value[F, A ++ B]): Either[Value[F, A], Value[F, B]] =
    value match
      case Value.Left(a)  => scala.Left(a)
      case Value.Right(b) => scala.Right(b)
      case Ext(_) => UnhandledCase.raise(s"$value") // TODO: require evidence for F that makes it compliant

  def extractInPortId[F[_], A](value: Value[F, Reading[A]]): PromiseId[A] =
    value match
      case ReadingInput(pa) => pa
      case Ext(_) => UnhandledCase.raise(s"$value") // TODO: require evidence for F that makes it compliant

  given zippableValue[F[_]]: Zippable[**, Value[F, _]] with
    override def zip[A, B](fa: Value[F, A], fb: Value[F, B]): Value[F, A ** B] =
      Pair(fa, fb)

  given unzippableValue[F[_]](using Unzippable[**, F]): Unzippable[**, Value[F, _]] with
    override def unzip[A, B](fab: Value[F, A ** B]): (Value[F, A], Value[F, B]) =
      Value.unpair(fab)
