package libretto.lambda

import libretto.lambda.util.{BiInjective, TypeEq}
import libretto.lambda.util.TypeEq.Refl

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

  def focus[F[_], X](pos: Focus[<*>, F])(using
    in: BiInjective[<*>],
    ev: A =:= F[X],
  ): AForest.Focused[->, <*>, F, X, B] =
    import AForest.Focused

    pos match
      case Focus.Id() =>
        Focused.At(AForest.Punched.Id(), this.from[X](using ev.flip))
      case Focus.Fst(pos1) =>
        focusFst(pos1)
      case Focus.Snd(pos2) =>
        focusSnd(pos2)

  protected def focusFst[F1[_], X, A2](
    f1: Focus[<*>, F1],
  )(using
    BiInjective[<*>],
    A =:= (F1[X] <*> A2),
  ): AForest.Focused[->, <*>, [x] =>> F1[x] <*> A2, X, B]

  protected def focusSnd[A1, F2[_], X](
    f2: Focus[<*>, F2],
  )(using
    BiInjective[<*>],
    A =:= (A1 <*> F2[X]),
  ): AForest.Focused[->, <*>, [x] =>> A1 <*> F2[x], X, B]

  def from[Z](using ev: Z =:= A): AForest[->, <*>, Z, B] =
    ev.substituteContra[AForest[->, <*>, _, B]](this)
}

object AForest {
  case class Empty[->[_, _], <*>[_, _], A]() extends AForest[->, <*>, A, A] {
    override def nonEmpty = false

    override protected def focusFst[F1[_], X, A2](f1: Focus[<*>, F1])(using BiInjective[<*>], A =:= F1[X] <*> A2): Focused[->, <*>, [x] =>> F1[x] <*> A2, X, A] =
      UnhandledCase.raise(s"AForest.Empty.focusFst")

    override protected def focusSnd[A1, F2[_], X](f2: Focus[<*>, F2])(using BiInjective[<*>], A =:= A1 <*> F2[X]): Focused[->, <*>, [x] =>> A1 <*> F2[x], X, A] =
      UnhandledCase.raise(s"AForest.Empty.focusSnd")
  }

  sealed trait NonEmpty[->[_, _], <*>[_, _], A, B] extends AForest[->, <*>, A, B] {
    override def nonEmpty = true
  }

  case class Node[->[_, _], <*>[_, _], A, X, B](
    value: A -> X,
    children: AForest[->, <*>, X, B],
  ) extends AForest.NonEmpty[->, <*>, A, B] {
    override protected def focusFst[F1[_], X, A2](f1: Focus[<*>, F1])(using BiInjective[<*>], A =:= F1[X] <*> A2): Focused[->, <*>, [x] =>> F1[x] <*> A2, X, B] =
      UnhandledCase.raise(s"Node.focusFst")

    override protected def focusSnd[A1, F2[_], X](f2: Focus[<*>, F2])(using BiInjective[<*>], A =:= A1 <*> F2[X]): Focused[->, <*>, [x] =>> A1 <*> F2[x], X, B] =
      UnhandledCase.raise(s"Node.focusSnd")
  }

  case class Par[->[_, _], <*>[_, _], A1, A2, B1, B2] private[AForest](
    f1: AForest[->, <*>, A1, B1],
    f2: AForest[->, <*>, A2, B2],
  ) extends AForest.NonEmpty[->, <*>, A1 <*> A2, B1 <*> B2] {
    require(f1.nonEmpty || f2.nonEmpty)

    override protected def focusFst[F1[_], X, Y](pos1: Focus[<*>, F1])(using
      in: BiInjective[<*>],
      ev: A1 <*> A2 =:= F1[X] <*> Y,
    ): Focused[->, <*>, [x] =>> F1[x] <*> Y, X, B1 <*> B2] =
      ev match { case BiInjective[<*>](ev1, TypeEq(Refl())) =>
        given (A1 =:= F1[X]) = ev1
        f1.focus(pos1).inFst(f2)
      }

    override protected def focusSnd[X, F2[_], Y](pos2: Focus[<*>, F2])(using
      in: BiInjective[<*>],
      ev: A1 <*> A2 =:= X <*> F2[Y],
    ): Focused[->, <*>, [x] =>> X <*> F2[x], Y, B1 <*> B2] =
      ev match { case BiInjective[<*>](TypeEq(Refl()), ev2) =>
        given (A2 =:= F2[Y]) = ev2
        f2.focus(pos2).inSnd(f1)
      }
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

    def inFst[T, U](snd: AForest[->, <*>, T, U]): Punched[->, <*>, [x] =>> F[x] <*> T, [y] =>> G[y] <*> U] =
      Punched.Fst(this, snd)

    def inSnd[T, U](fst: AForest[->, <*>, T, U]): Punched[->, <*>, [x] =>> T <*> F[x], [y] =>> U <*> G[y]] =
      Punched.Snd(fst, this)
  }

  object Punched {
    case class Id[->[_, _], <*>[_, _]]() extends Punched[->, <*>, [x] =>> x, [x] =>> x] {
      override def apply[T]: AForest[->, <*>, T, T] = Empty()
      override def plug[T, U](f: AForest[->, <*>, T, U]): AForest[->, <*>, T, U] = f
      override def inFocus: Focus[<*>, [x] =>> x] = Focus.id
      override def outFocus: Focus[<*>, [x] =>> x] = Focus.id
    }

    case class Fst[->[_, _], <*>[_, _], F[_], A2, G[_], B2](
      fst: Punched[->, <*>, F, G],
      snd: AForest[->, <*>, A2, B2],
    ) extends Punched[->, <*>, [x] =>> F[x] <*> A2, [y] =>> G[y] <*> B2] {
      override def apply[T]: AForest[->, <*>, F[T] <*> A2, G[T] <*> B2] =
        par(fst[T], snd)

      override def plug[T, U](f: AForest[->, <*>, T, U]): AForest[->, <*>, F[T] <*> A2, G[U] <*> B2] =
        par(fst.plug(f), snd)

      override def inFocus: Focus[<*>, [x] =>> F[x] <*> A2] =
        fst.inFocus.inFst[A2]

      override def outFocus: Focus[<*>, [y] =>> G[y] <*> B2] =
        fst.outFocus.inFst[B2]
    }

    case class Snd[->[_, _], <*>[_, _], A1, F[_], B1, G[_]](
      fst: AForest[->, <*>, A1, B1],
      snd: Punched[->, <*>, F, G],
    ) extends Punched[->, <*>, [x] =>> A1 <*> F[x], [y] =>> B1 <*> G[y]] {
      override def apply[T]: AForest[->, <*>, A1 <*> F[T], B1 <*> G[T]] =
        par(fst, snd[T])

      override def plug[T, U](f: AForest[->, <*>, T, U]): AForest[->, <*>, A1 <*> F[T], B1 <*> G[U]] =
        par(fst, snd.plug(f))

      override def inFocus: Focus[<*>, [x] =>> A1 <*> F[x]] =
        snd.inFocus.inSnd[A1]

      override def outFocus: Focus[<*>, [y] =>> B1 <*> G[y]] =
        snd.outFocus.inSnd[B1]
    }
  }

  sealed trait Focused[->[_, _], <*>[_, _], F[_], X, B] {
    def inFst[T, U](snd: AForest[->, <*>, T, U]): Focused[->, <*>, [x] =>> F[x] <*> T, X, B <*> U]
    def inSnd[T, U](fst: AForest[->, <*>, T, U]): Focused[->, <*>, [x] =>> T <*> F[x], X, U <*> B]
  }

  object Focused {
    case class At[->[_, _], <*>[_, _], F[_], X, Y, G[_]](
      context: Punched[->, <*>, F, G],
      target: AForest[->, <*>, X, Y],
    ) extends Focused[->, <*>, F, X, G[Y]] {
      override def inFst[T, U](snd: AForest[->, <*>, T, U]): Focused[->, <*>, [x] =>> F[x] <*> T, X, G[Y] <*> U] =
        Focused.At[->, <*>, [x] =>> F[x] <*> T, X, Y, [y] =>> G[y] <*> U](context.inFst(snd), target)

      override def inSnd[T, U](fst: AForest[->, <*>, T, U]): Focused[->, <*>, [x] =>> T <*> F[x], X, U <*> G[Y]] =
        Focused.At[->, <*>, [x] =>> T <*> F[x], X, Y, [y] =>> U <*> G[y]](context.inSnd(fst), target)
    }

    case class IntoNode[->[_, _], <*>[_, _], FO[_], FI[_], X, P, Y, GO[_]](
      outerF: Focus[<*>, FO],
      innerF: Focus.Proper[<*>, FI],
      target: Node[->, <*>, FI[X], P, Y],
    ) extends Focused[->, <*>, [x] =>> FO[FI[x]], X, GO[Y]] {
      override def inFst[T, U](snd: AForest[->, <*>, T, U]): Focused[->, <*>, [x] =>> FO[FI[x]] <*> T, X, GO[Y] <*> U] =
        IntoNode[->, <*>, [x] =>> FO[x] <*> T, FI, X, P, Y, [x] =>> GO[x] <*> U](outerF.inFst[T], innerF, target)

      override def inSnd[T, U](fst: AForest[->, <*>, T, U]): Focused[->, <*>, [x] =>> T <*> FO[FI[x]], X, U <*> GO[Y]] =
        IntoNode[->, <*>, [x] =>> T <*> FO[x], FI, X, P, Y, [x] =>> U <*> GO[x]](outerF.inSnd[T], innerF, target)
    }
  }
}
