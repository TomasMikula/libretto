package libretto.lambda.examples.workflow.generic.vis

case class TrapezoidArea[X, Y](
  src: EdgeStretch[X],
  tgt: EdgeStretch[Y],
  fill: Color | PredefinedFill,
)
