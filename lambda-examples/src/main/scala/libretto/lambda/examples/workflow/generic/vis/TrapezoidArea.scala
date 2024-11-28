package libretto.lambda.examples.workflow.generic.vis

case class TrapezoidArea[X, Y](
  src: EdgeStretch[X],
  tgt: EdgeStretch[Y],
  fill: Color | PredefinedFill,
)

object TrapezoidArea {
  def apply[x, X, y, Y](
    src: EdgeSegment[x, X],
    tgt: EdgeSegment[y, Y],
    fill: Color | PredefinedFill,
  ): TrapezoidArea[X, Y] =
    TrapezoidArea(
      EdgeStretch.segment(src),
      EdgeStretch.segment(tgt),
      fill,
    )
}
