package libretto.lambda.examples.workflow.generic.vis

sealed trait TrapezoidArea[X, Y]

object TrapezoidArea {
  case class Impl[X0, X, Y0, Y](
    src: EdgeSegment[X0, X] | EdgeSegment.SubWire[X],
    tgt: EdgeSegment[Y0, Y] | EdgeSegment.SubWire[Y],
    fill: Color,
  ) extends TrapezoidArea[X, Y]

  def apply[X0, X, Y0, Y](
    src: EdgeSegment[X0, X] | EdgeSegment.SubWire[X],
    tgt: EdgeSegment[Y0, Y] | EdgeSegment.SubWire[Y],
    fill: Color,
  ): TrapezoidArea[X, Y] =
    Impl(src, tgt, fill)
}
