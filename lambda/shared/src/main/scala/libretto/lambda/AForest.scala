package libretto.lambda

/** A forest-like structured composition of arrows.
 *
 * For example,
 *
 * ```
 *     A               C
 *     |     <*>       |
 *     v               v
 *     B           D  <*>  (E <*> F)
 *                          |
 *                          v
 *                          G
 * ```
 *
 * is an `AForest[->, <*>, A <*> C, B <*> (D <*> (G <*> F))]`
 */
sealed trait AForest[->[_, _], <*>[_, _], A, B] {
  def nonEmpty: Boolean

  def inFst[Y]: AForest[->, <*>, A <*> Y, B <*> Y] =
    AForest.par(this, AForest.Empty())

  def inSnd[X]: AForest[->, <*>, X <*> A, X <*> B] =
    AForest.par(AForest.Empty(), this)
}

object AForest {
  case class Empty[->[_, _], <*>[_, _], A]() extends AForest[->, <*>, A, A] {
    override def nonEmpty = false
  }

  sealed trait NonEmpty[->[_, _], <*>[_, _], A, B] extends AForest[->, <*>, A, B] {
    override def nonEmpty = true
  }

  case class Node[->[_, _], <*>[_, _], A, X, B](
    value: A -> X,
    children: AForest[->, <*>, X, B],
  ) extends AForest.NonEmpty[->, <*>, A, B]

  case class Par[->[_, _], <*>[_, _], A1, A2, B1, B2] private[AForest](
    f1: AForest[->, <*>, A1, B1],
    f2: AForest[->, <*>, A2, B2],
  ) extends AForest.NonEmpty[->, <*>, A1 <*> A2, B1 <*> B2] {
    require(f1.nonEmpty || f2.nonEmpty)
  }

  def par[->[_, _], <*>[_, _], A1, A2, B1, B2](
    f1: AForest[->, <*>, A1, B1],
    f2: AForest[->, <*>, A2, B2],
  ): AForest[->, <*>, A1 <*> A2, B1 <*> B2] =
    (f1, f2) match
      case (Empty(), Empty()) => Empty()
      case (f1, f2)           => Par(f1, f2)
}
