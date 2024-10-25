package libretto.lambda

import libretto.lambda.util.StaticValue

/** Witnesses that `Items` is a list of `name :: type` pairs,
 * i.e. that `Items` is of the form `(Name1 :: T1) || ... || (NameN :: TN)`.
 */
sealed trait ItemList[||[_, _], ::[_, _], Items]

object ItemList {
  case class Single[||[_, _], ::[_, _], Lbl <: String, A](
    lbl: Lbl,
  ) extends ItemList[||, ::, Lbl :: A]

  case class Snoc[||[_, _], ::[_, _], Init, Lbl <: String, A](
    init: ItemList[||, ::, Init],
    lbl: Lbl,
  ) extends ItemList[||, ::, Init || (Lbl :: A)]

  given single[||[_, _], ::[_, _], Lbl <: String, A](using
    lbl: StaticValue[Lbl],
  ): ItemList[||, ::, Lbl :: A] =
    Single(lbl.value)

  given snoc[||[_, _], ::[_, _], Init, Lbl <: String, A](using
    init: ItemList[||, ::, Init],
    lbl: StaticValue[Lbl],
  ): ItemList[||, ::, Init || (Lbl :: A)] =
    Snoc(init, lbl.value)
}