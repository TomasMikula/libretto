package libretto.lambda

import libretto.lambda.util.{Functional, TypeEq}
import libretto.lambda.util.TypeEq.Refl

/** Witnesses that when item names are removed from non-empty item list
 *
 *   `As = name1 :: A1 || ... || nameN :: An`
 *
 * and field separator is changed from `||` to `∙`,
 * we obtain
 *
 *   `Bs = Nil ∙ B1 ∙ ... ∙ Bn`
 *
 */
sealed trait DropNames[||[_, _], ::[_, _], ∙[_, _], Nil, As, Bs] {
  def inInit[NameX, X]: DropNames[||, ::, ∙, Nil, As || NameX :: X, Bs ∙ X] =
    DropNames.Snoc(this)
}

object DropNames {
  case class Single[||[_, _], ::[_, _], ∙[_, _], Nil, NameA, A]()
    extends DropNames[||, ::, ∙, Nil, NameA :: A, Nil ∙ A]

  case class Snoc[||[_, _], ::[_, _], ∙[_, _], Nil, Init, NameT, T, Init0](
    init: DropNames[||, ::, ∙, Nil, Init, Init0],
  ) extends DropNames[||, ::, ∙, Nil, Init || NameT :: T, Init0 ∙ T]

  given [||[_, _], ::[_, _], ∙[_, _], Nil, A, B]: Functional[DropNames[||, ::, ∙, Nil, _, _]] with {
    override def uniqueOutputType[A, B, C](
      f: DropNames[||, ::, ∙, Nil, A, B],
      g: DropNames[||, ::, ∙, Nil, A, C],
    ): B =:= C =
      (f, g) match
        case (Single()   , Single()   ) => summon
        case (Snoc(fInit), Snoc(gInit)) => uniqueOutputType(fInit, gInit) match { case TypeEq(Refl()) => summon }
        case _                          => throw AssertionError("Impossible if `||` and `::` are distinct class types")
  }
}
