package libretto.lambda.examples.workflow.generic.vis

import DefaultDimensions.Length

/** Refine and/or coarsen parts of `X` to get `Y`. */
sealed trait Morph[X, Y] {
  def invert: Morph[Y, X]
  def length: Length
}

object Morph {
  case class Id[X](desc: EdgeDesc[X]) extends Morph[X, X] {
    override def invert: Morph[X, X] = this
    override def length: Length = Length.one
  }

  case class Refine[X, Y](f: X IsRefinedBy Y) extends Morph[X, Y] {
    override def invert: Morph[Y, X] =
      Unrefine(f)

    override def length: Length =
      lengthOf(f)
  }

  case class Unrefine[X, Y](f: Y IsRefinedBy X) extends Morph[X, Y] {
    override def invert: Morph[Y, X] =
      Refine(f)

    override def length: Length =
      lengthOf(f)
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

  def id[X](using EdgeDesc[X]): Morph[X, X] =
    Id(summon)

  def par[∙[_, _]]: ParBuilder[∙] =
    ParBuilder[∙]

  class ParBuilder[∙[_, _]]:
    def apply[X1, X2, Y1, Y2](
      f1: Morph[X1, Y1],
      f2: Morph[X2, Y2],
    ): Morph[X1 ∙ X2, Y1 ∙ Y2] =
      Par(f1, f2)

  private def lengthOf[X, Y](f: X IsRefinedBy Y): Length =
    f match
      case IsRefinedBy.Id(desc) =>
        Length.one
      case IsRefinedBy.Initial(desc) =>
        depthOf(desc)
      case IsRefinedBy.Pairwise(f1, f2) =>
        Length.max(lengthOf(f1), lengthOf(f2))

  private def depthOf[X](desc: EdgeDesc[X]): Length =
    desc match
      case EdgeDesc.SingleWire =>
        Length.one
      case EdgeDesc.Binary(x1, x2) =>
        Length.cram(
          Length.one,
          Length.max(depthOf(x1), depthOf(x2))
        )

}
