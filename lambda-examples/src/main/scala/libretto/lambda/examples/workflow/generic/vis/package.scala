package libretto.lambda.examples.workflow.generic.vis

/** Used in phantom position to represent a single (further undiscriminated wire), approximating any type. */
sealed trait Wire
object Wire:
  def isNotPair[X, Y](using ev: Wire =:= (X, Y)): Nothing =
    throw AssertionError("Impossible: Wire =:= Tuple2[X, Y]")

  def isNotBinary[∙[_, _], X, Y](using
    ev: Wire =:= (X ∙ Y),
    // TODO: require evidence that ∙ is a class type.
    // Otherwise unsound, e.g. for
    //   type ∙[A, B] = Wire
  ): Nothing =
    throw AssertionError("Impossible: Wire =:= (X ∙ Y)")

val DefaultDimensions: Dimensions =
  SquaredDimensions
