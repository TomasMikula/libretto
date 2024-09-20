package libretto.lambda.examples.workflow.generic.vis

import DefaultDimensions.Length

/** Refine and/or coarsen parts of `X` to get `Y`. */
sealed trait Morph[X, Y] {
  def invert: Morph[Y, X]
  def length: Length
}

object Morph {
  case class Id[X]() extends Morph[X, X] {
    override def invert: Morph[X, X] = this
    override def length: Length = Length.zero
  }

  case class Co[X, Y](f: X IsRefinedBy Y) extends Morph[X, Y] {
    override def invert: Morph[Y, X] =
      Contra(f)

    override def length: Length =
      // TODO
      Length.one
  }

  case class Contra[X, Y](f: Y IsRefinedBy X) extends Morph[X, Y] {
    override def invert: Morph[Y, X] =
      Co(f)

    override def length: Length =
      // TODO
      Length.one
  }

  case class Par[∙[_, _], X1, X2, Y1, Y2](
    f1: Morph[X1, Y1],
    f2: Morph[X2, Y2],
  ) extends Morph[X1 ∙ X2, Y1 ∙ Y2] {
    override def invert: Morph[Y1 ∙ Y2, X1 ∙ X2] =
      Par(f1.invert, f2.invert)

    override def length: Length =
      Length.max(f1.length, f2.length)
  }

  def id[X]: Morph[X, X] =
    Id()

  def par[∙[_, _]]: ParBuilder[∙] =
    ParBuilder[∙]

  class ParBuilder[∙[_, _]]:
    def apply[X1, X2, Y1, Y2](
      f1: Morph[X1, Y1],
      f2: Morph[X2, Y2],
    ): Morph[X1 ∙ X2, Y1 ∙ Y2] =
      Par(f1, f2)
}
