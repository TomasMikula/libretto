package libretto.lambda.examples.workflow.generic.vis

/** Used in phantom position to represent a single (further undiscriminated wire), approximating any type. */
sealed trait Wire
object Wire:
  def isNotPair[X, Y](using ev: Wire =:= (X, Y)): Nothing =
    throw AssertionError("Impossible: Wire =:= Tuple2[X, Y]")

val DefaultDimensions: Dimensions =
  SquaredDimensions
