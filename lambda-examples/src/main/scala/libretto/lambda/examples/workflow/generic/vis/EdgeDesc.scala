package libretto.lambda.examples.workflow.generic.vis

import DefaultDimensions.Length

sealed trait EdgeDesc[X]:
  def depth: Length

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
