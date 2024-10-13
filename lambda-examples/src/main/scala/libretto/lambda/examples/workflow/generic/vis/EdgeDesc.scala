package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.lang.{++, **}

import DefaultDimensions.Length

sealed trait EdgeDesc[X] {
  def depth: Length

  def combine[∙[_, _]](using OpTag[∙]): BinaryBuilder[∙] =
    BinaryBuilder[∙]

  class BinaryBuilder[∙[_, _]](using op: OpTag[∙]) {
    def apply[Y](that: EdgeDesc[Y]): EdgeDesc[X ∙ Y] =
      EdgeDesc.this ∙ that
  }

  def ∙[∙[_, _], Y](that: EdgeDesc[Y])(using OpTag[∙]): EdgeDesc[X ∙ Y] =
    EdgeDesc.Binary[∙, X, Y](summon, this, that)

  def ++[Y](that: EdgeDesc[Y]): EdgeDesc[X ++ Y] =
    this ∙ that

  def **[Y](that: EdgeDesc[Y]): EdgeDesc[X ** Y] =
    this ∙ that
}

object EdgeDesc {
  case object SingleWire extends EdgeDesc[Wire]:
    override def depth: Length =
      Length.one

  sealed trait Composite[X] extends EdgeDesc[X]

  case class Binary[∙[_, _], X1, X2](
    op: OpTag[∙],
    x1: EdgeDesc[X1],
    x2: EdgeDesc[X2],
  ) extends EdgeDesc.Composite[X1 ∙ X2]:
    override def depth: Length =
      (x1, x2) match
        case (SingleWire, SingleWire) =>
          Length.one
        case _ =>
          Length.cram(
            Length.one,
            Length.max(x1.depth, x2.depth)
          )

  given wire: EdgeDesc[Wire] =
    SingleWire

  def binary[∙[_, _], X1, X2](using
    op: OpTag[∙],
  )(
    x1: EdgeDesc[X1],
    x2: EdgeDesc[X2],
  ): EdgeDesc[X1 ∙ X2] =
    Binary(op, x1, x2)
}
