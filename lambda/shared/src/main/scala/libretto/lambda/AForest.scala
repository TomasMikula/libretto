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

  def focus[F[_], X](pos: Focus[<*>, F])(using ev: A =:= F[X]): AForest.Focused[->, <*>, F, X, B] =
    import AForest.Focused

    pos match
      case Focus.Id() =>
        Focused.At(AForest.Punched.Id(), this.from[X](using ev.flip))
      case Focus.Fst(p1) =>
        UnhandledCase.raise(s"AForest.focus($pos)")
      case Focus.Snd(p2) =>
        UnhandledCase.raise(s"AForest.focus($pos)")

  def from[Z](using ev: Z =:= A): AForest[->, <*>, Z, B] =
    ev.substituteContra[AForest[->, <*>, _, B]](this)
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

  sealed trait Punched[->[_, _], <*>[_, _], F[_], G[_]] {
    def apply[T]: AForest[->, <*>, F[T], G[T]]
    def plug[T, U](f: AForest[->, <*>, T, U]): AForest[->, <*>, F[T], G[U]]
    def inFocus: Focus[<*>, F]
    def outFocus: Focus[<*>, G]
  }

  object Punched {
    case class Id[->[_, _], <*>[_, _]]() extends Punched[->, <*>, [x] =>> x, [x] =>> x] {
      override def apply[T]: AForest[->, <*>, T, T] = Empty()
      override def plug[T, U](f: AForest[->, <*>, T, U]): AForest[->, <*>, T, U] = f
      override def inFocus: Focus[<*>, [x] =>> x] = Focus.id
      override def outFocus: Focus[<*>, [x] =>> x] = Focus.id
    }
  }

  sealed trait Focused[->[_, _], <*>[_, _], F[_], X, B]
  object Focused {
    case class At[->[_, _], <*>[_, _], F[_], X, Y, G[_]](
      context: Punched[->, <*>, F, G],
      target: AForest[->, <*>, X, Y],
    ) extends Focused[->, <*>, F, X, G[Y]]

    case class IntoNode[->[_, _], <*>[_, _], FO[_], FI[_], X, P, Y](
      outerF: Focus[<*>, FO],
      innerF: Focus.Proper[<*>, FI],
      target: Node[->, <*>, FI[X], P, Y],
    ) extends Focused[->, <*>, [x] =>> FO[FI[x]], X, FO[Y]]
  }
}
