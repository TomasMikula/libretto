package libretto.mashup.dsl

import libretto.StarterKit.{dsl => impl}
import libretto.StarterKit.dsl.-⚬

case class Fun[A, B](value: A -⚬ B)

object Fun {
  opaque type or[A, B] = impl.|+|[A, B]

  /** Higher-order function, i.e. one that occurs on input or output of [[Blueprint]]s. */
  type -->[A, B]

  def id[A]: Fun[A, A] =
    Fun(impl.id[A])

  def left[A, B]: Fun[A, A or B] =
    Fun(impl.injectL[A, B])

  def right[A, B]: Fun[B, A or B] =
    Fun(impl.injectR[A, B])
}
