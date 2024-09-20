package libretto.lambda.examples.workflow.generic.vis

sealed trait IOLayout[I, O] {
  import IOLayout.*

  def pixelBreadth: Px
  def inEdge: EdgeLayout[I]
  def outEdge: EdgeLayout[O]
  def *(k: Int): IOLayout[I, O]

  def separate: (EdgeLayout[I], EdgeLayout[O]) =
    (inEdge, outEdge)
}

object IOLayout {
  sealed trait EdgeLayout[X] {
    def pixelBreadth: Px
  }

  object EdgeLayout {
    case class Unimplemented[X](pixelBreadth: Px) extends EdgeLayout[X]

    case class Par[∙[_, _], X1, X2](
      l1: EdgeLayout[X1],
      l2: EdgeLayout[X2],
    ) extends EdgeLayout[X1 ∙ X2] {
      override def pixelBreadth: Px =
        l1.pixelBreadth + l2.pixelBreadth
    }
  }

  case class Unimplemented[X, Y](pixelBreadth: Px) extends IOLayout[X, Y] {
    override def inEdge: EdgeLayout[X] =
      EdgeLayout.Unimplemented(pixelBreadth)

    override def outEdge: EdgeLayout[Y] =
      EdgeLayout.Unimplemented(pixelBreadth)

    override def *(k: Int): IOLayout[X, Y] =
      require(k > 0)
      Unimplemented(pixelBreadth * k)
  }

  case class Par[∙[_, _], I1, I2, O1, O2](
    l1: IOLayout[I1, O1],
    l2: IOLayout[I2, O2],
  ) extends IOLayout[I1 ∙ I2, O1 ∙ O2] {
    override def pixelBreadth: Px =
      l1.pixelBreadth + l2.pixelBreadth

    override def inEdge: EdgeLayout[I1 ∙ I2] =
      EdgeLayout.Par(l1.inEdge, l2.inEdge)

    override def outEdge: EdgeLayout[O1 ∙ O2] =
      EdgeLayout.Par(l1.outEdge, l2.outEdge)

    override def *(k: Int): IOLayout[I1 ∙ I2, O1 ∙ O2] =
      require(k > 0)
      Par(l1 * k, l2 * k)
  }
}
