package libretto.lambda

sealed trait Multiplier[|*|[_, _], A, A1]

object Multiplier {
  case class Id[|*|[_, _], A]() extends Multiplier[|*|, A, A]
  case class Dup[|*|[_, _], A, A1, A2](
    f: Multiplier[|*|, A, A1],
    g: Multiplier[|*|, A, A2],
  ) extends Multiplier[|*|, A, A1 |*| A2]
}
