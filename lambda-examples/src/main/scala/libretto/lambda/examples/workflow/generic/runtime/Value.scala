package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.examples.workflow.generic.lang.**

enum Value[F[_], A]:
  case Pair[F[_], A1, A2](
    a1: Value[F, A1],
    a2: Value[F, A2],
  ) extends Value[F, A1 ** A2]

  /** Extension point for domain-specific values. */
  case Ext(value: F[A])

  def **[B](that: Value[F, B]): Value[F, A ** B] =
    Pair(this, that)
