package libretto.lambda

/** A collection of arrows of the form `Ai --> B`, with `A = A1 <+> ... <+> An`. */
sealed trait Sink[-->[_, _], <+>[_, _], A, B]

object Sink {
  case class Arrow[-->[_, _], <+>[_, _], A, B](
    f: A --> B,
  ) extends Sink[-->, <+>, A, B]

  case class Join[-->[_, _], <+>[_, _], A1, A2, B](
    s1: Sink[-->, <+>, A1, B],
    s2: Sink[-->, <+>, A2, B],
  ) extends Sink[-->, <+>, A1 <+> A2, B]
}
