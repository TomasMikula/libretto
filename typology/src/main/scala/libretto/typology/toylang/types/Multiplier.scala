package libretto.typology.toylang.types

sealed trait Multiplier[×[_, _], A, AA] {

}

object Multiplier {
  case class Id[×[_, _], A]() extends Multiplier[×, A, A]

  case class Dup[×[_, _], A, A1, A2](
    m1: Multiplier[×, A, A1],
    m2: Multiplier[×, A, A2],
  ) extends Multiplier[×, A, A1 × A2]
}
