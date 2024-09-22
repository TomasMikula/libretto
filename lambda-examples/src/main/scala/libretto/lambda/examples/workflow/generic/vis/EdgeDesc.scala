package libretto.lambda.examples.workflow.generic.vis

sealed trait EdgeDesc[X]

object EdgeDesc {
  case object SingleWire extends EdgeDesc[Wire]

  case class Binary[∙[_, _], X1, X2](
    x1: EdgeDesc[X1],
    x2: EdgeDesc[X2],
  ) extends EdgeDesc[X1 ∙ X2]

  given wire: EdgeDesc[Wire] =
    SingleWire

  def binary[∙[_, _], X1, X2](
    x1: EdgeDesc[X1],
    x2: EdgeDesc[X2],
  ): EdgeDesc[X1 ∙ X2] =
    Binary(x1, x2)
}
