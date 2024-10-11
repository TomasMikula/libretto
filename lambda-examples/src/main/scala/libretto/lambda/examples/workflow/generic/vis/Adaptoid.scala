package libretto.lambda.examples.workflow.generic.vis

import DefaultDimensions.Length

/** Refine and/or coarsen parts of `X` to get `Y`. */
sealed trait Adaptoid[X, Y] {
  def invert: Adaptoid[Y, X]
  def length: Length
  def inDesc: EdgeDesc[X]
  def outDesc: EdgeDesc[Y]
}

object Adaptoid {
  case class Id[X](desc: EdgeDesc[X]) extends Adaptoid[X, X] {
    override def invert: Adaptoid[X, X] = this
    override def length: Length = Length.one
    override def inDesc: EdgeDesc[X] = desc
    override def outDesc: EdgeDesc[X] = desc
  }

  case class Expand[X, Y](f: X IsRefinedBy Y) extends Adaptoid[X, Y] {
    override def invert: Adaptoid[Y, X] =
      Collapse(f)

    override def length: Length =
      lengthOf(f)

    override def inDesc: EdgeDesc[X] = f.inDesc
    override def outDesc: EdgeDesc[Y] = f.outDesc
  }

  case class Collapse[X, Y](f: Y IsRefinedBy X) extends Adaptoid[X, Y] {
    override def invert: Adaptoid[Y, X] =
      Expand(f)

    override def length: Length =
      lengthOf(f)

    override def inDesc: EdgeDesc[X] = f.outDesc
    override def outDesc: EdgeDesc[Y] = f.inDesc
  }

  case class Par[∙[_, _], X1, X2, Y1, Y2](
    op: OpTag[∙],
    f1: Adaptoid[X1, Y1],
    f2: Adaptoid[X2, Y2],
  ) extends Adaptoid[X1 ∙ X2, Y1 ∙ Y2] {
    private given OpTag[∙] = op

    override def invert: Adaptoid[Y1 ∙ Y2, X1 ∙ X2] =
      Par(op, f1.invert, f2.invert)

    override def length: Length =
      Length.max(f1.length, f2.length)

    override def inDesc: EdgeDesc[X1 ∙ X2] = EdgeDesc.binary(f1.inDesc, f2.inDesc)
    override def outDesc: EdgeDesc[Y1 ∙ Y2] = EdgeDesc.binary(f1.outDesc, f2.outDesc)
  }

  def id[X](using EdgeDesc[X]): Adaptoid[X, X] =
    Id(summon)

  def par[∙[_, _]](using OpTag[∙]): ParBuilder[∙] =
    ParBuilder[∙]

  class ParBuilder[∙[_, _]](using op: OpTag[∙]):
    def apply[X1, X2, Y1, Y2](
      f1: Adaptoid[X1, Y1],
      f2: Adaptoid[X2, Y2],
    ): Adaptoid[X1 ∙ X2, Y1 ∙ Y2] =
      Par(op, f1, f2)

  private def lengthOf[X, Y](f: X IsRefinedBy Y): Length =
    f match
      case IsRefinedBy.Id(desc) =>
        Length.one
      case IsRefinedBy.Initial(desc) =>
        desc.depth
      case IsRefinedBy.Pairwise(_, f1, f2) =>
        Length.max(lengthOf(f1), lengthOf(f2))

}
