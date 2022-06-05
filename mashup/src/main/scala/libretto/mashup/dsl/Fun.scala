package libretto.mashup.dsl

sealed trait Fun[A, B]

object Fun {
  /** Higher-order function, i.e. one that occurs on input or output of [[Blueprint]]s. */
  type -->[A, B]
}
