package libretto.lambda.examples.workflow.generic.vis

import DefaultDimensions.Breadth
import IOLayout.EdgeLayout

sealed trait IOProportions[I, O] {
  def totalBreadth: Breadth
  def layout(availableBreadth: Px): (Int, IOLayout[I, O])
  def layoutFw(inLayout: EdgeLayout[I]): (Int, IOLayout[I, O])
  def layoutBw(outLayout: EdgeLayout[O]): (Int, IOLayout[I, O])
}

object IOProportions {
  case class Unimplemented[I, O](totalBreadth: Breadth) extends IOProportions[I, O] {
    override def layout(availableBreadth: Px): (Int, IOLayout[I, O]) =
      (1, IOLayout.Unimplemented(availableBreadth))

    override def layoutFw(inLayout: EdgeLayout[I]): (Int, IOLayout[I, O]) =
      (1, IOLayout.Unimplemented(inLayout.pixelBreadth))

    override def layoutBw(outLayout: EdgeLayout[O]): (Int, IOLayout[I, O]) =
      (1, IOLayout.Unimplemented(outLayout.pixelBreadth))
  }
}
