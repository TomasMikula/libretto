package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.Unzippable
import libretto.lambda.examples.workflow.generic.lang.**

enum Value[F[_], A]:
  case One[F[_]]() extends Value[F, Unit]
  case Pair[F[_], A1, A2](
    a1: Value[F, A1],
    a2: Value[F, A2],
  ) extends Value[F, A1 ** A2]

  /** Extension point for domain-specific values. */
  case Ext(value: F[A])

  def **[B](that: Value[F, B]): Value[F, A ** B] =
    Pair(this, that)

object Value:
  def unit[F[_]]: Value[F, Unit] =
    Value.One()

  def unpair[F[_], A, B](value: Value[F, A ** B])(using F: Unzippable[**, F]): (Value[F, A], Value[F, B]) =
    value match
      case Pair(a, b) =>
        (a, b)
      case Ext(value) =>
        val (a, b) = F.unzip(value)
        (Ext(a), Ext(b))
