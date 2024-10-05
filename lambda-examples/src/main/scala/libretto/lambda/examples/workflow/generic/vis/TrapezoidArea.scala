package libretto.lambda.examples.workflow.generic.vis

case class TrapezoidArea[X, Y](
  src: EdgeSegment[?, X],
  tgt: EdgeSegment[?, Y],
  fill: Color,
)
