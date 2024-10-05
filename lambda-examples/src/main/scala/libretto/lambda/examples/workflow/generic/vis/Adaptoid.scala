package libretto.lambda.examples.workflow.generic.vis

import DefaultDimensions.Length

/** Refine and/or coarsen parts of `X` to get `Y`. */
sealed trait Adaptoid[X, Y] {
  def invert: Adaptoid[Y, X]
  def length: Length
}

object Adaptoid {
  case class Id[X](desc: EdgeDesc[X]) extends Adaptoid[X, X] {
    override def invert: Adaptoid[X, X] = this
    override def length: Length = Length.one
  }

  case class Expand[X, Y](f: X IsRefinedBy Y) extends Adaptoid[X, Y] {
    override def invert: Adaptoid[Y, X] =
      Collapse(f)

    override def length: Length =
      lengthOf(f)
  }

  case class Collapse[X, Y](f: Y IsRefinedBy X) extends Adaptoid[X, Y] {
    override def invert: Adaptoid[Y, X] =
      Expand(f)

    override def length: Length =
      lengthOf(f)
  }

  case class Par[∙[_, _], X1, X2, Y1, Y2](
    f1: Adaptoid[X1, Y1],
    f2: Adaptoid[X2, Y2],
  ) extends Adaptoid[X1 ∙ X2, Y1 ∙ Y2] {
    override def invert: Adaptoid[Y1 ∙ Y2, X1 ∙ X2] =
      Par(f1.invert, f2.invert)

    override def length: Length =
      Length.max(f1.length, f2.length)
  }

  def id[X](using EdgeDesc[X]): Adaptoid[X, X] =
    Id(summon)

  def par[∙[_, _]]: ParBuilder[∙] =
    ParBuilder[∙]

  class ParBuilder[∙[_, _]]:
    def apply[X1, X2, Y1, Y2](
      f1: Adaptoid[X1, Y1],
      f2: Adaptoid[X2, Y2],
    ): Adaptoid[X1 ∙ X2, Y1 ∙ Y2] =
      Par(f1, f2)

  private def lengthOf[X, Y](f: X IsRefinedBy Y): Length =
    f match
      case IsRefinedBy.Id(desc) =>
        Length.one
      case IsRefinedBy.Initial(desc) =>
        desc.depth
      case IsRefinedBy.Pairwise(f1, f2) =>
        Length.max(lengthOf(f1), lengthOf(f2))

}
