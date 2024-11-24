package libretto.lambda.examples.workflow.generic.vis

/** Used in phantom position to represent a single (further undiscriminated wire), approximating any type. */
sealed trait Wire
object Wire:
  def isNotPair[X, Y](using ev: Wire =:= (X, Y)): Nothing =
    throw AssertionError("Impossible: Wire =:= Tuple2[X, Y]")

  def isNotUnary[F[_], X](using
    Wire =:= F[X],
    // TODO: require evidence that F is a class type.
    // Otherwise unsound, e.g. for
    //   type F[A] = Wire
  ): Nothing =
    throw AssertionError("Impossible: Wire =:= F[X]")

  def isNotBinary[∙[_, _], X, Y](using
    ev: Wire =:= (X ∙ Y),
    // TODO: require evidence that ∙ is a class type.
    // Otherwise unsound, e.g. for
    //   type ∙[A, B] = Wire
  ): Nothing =
    throw AssertionError("Impossible: Wire =:= (X ∙ Y)")

/** Used to denote the first and inner-most element of nested tuples.
 * The purpose of marking the first element is to be able to distinguish `Only[(A, B)]` from `(A, B)`:
 *
 * ```
 * (Only[(A, B)], C)
 * ```
 *
 * cannot be confused with
 *
 * ```
 * ((A, B), C)
 * ```
 */
type Only[X] = (EmptyTuple, X)

def pairIsNotEmptyTuple[X, Y](using (X, Y) =:= EmptyTuple): Nothing =
  throw AssertionError("Impossible: (X, Y) =:= EmptyTuple")

val DefaultDimensions: Dimensions =
  SquaredDimensions
