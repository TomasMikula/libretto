package libretto.lambda

import libretto.lambda.util.{BiInjective, Injective, Masked, TypeEq}
import libretto.lambda.util.TypeEq.Refl

/** Witnesses that `FA` is a product (**) of F[x1], F[x2], ... and `A` is the product of x1, x2, ... (i.e. after stripping the F's). */
sealed trait StripF[**[_, _], F[_], FA, A] {
  infix def uniqueOutType[B](that: StripF[**, F, FA, B])(fIsNotPair: [X, Y, Z] => (F[X] =:= (Y ** Z)) => Nothing)(using
    BiInjective[**],
    Injective[F],
  ): A =:= B

  infix def zip[FB, B](that: StripF[**, F, FB, B]): StripF[**, F, FA ** FB, A ** B] =
    StripF.Par(this, that)

  def maskInput: Masked[StripF[**, F, _, A], FA] =
    Masked(this)

  def from[Z](using ev: Z =:= FA): StripF[**, F, Z, A] =
    ev.substituteContra[StripF[**, F, _, A]](this)

  def focusFirst[R](callback: [G[_], X] => (Focus[**, G], FA =:= G[F[X]]) => R): R
}

object StripF {
  case class Single[**[_, _], F[_], A]() extends StripF[**, F, F[A], A] {
    override def uniqueOutType[B](that: StripF[**, F, F[A], B])(fIsNotPair: [X, Y, Z] => (F[X] =:= (Y ** Z)) => Nothing)(using
      BiInjective[**],
      Injective[F],
    ): A =:= B =
      that.maskInput.visit[A =:= B]([FB] => (that: StripF[**, F, FB, B], ev: FB =:= F[A]) => {
        that match {
          case _: Single[pr, f, b] =>
            (summon[F[b] =:= FB] andThen ev) match { case Injective[F](TypeEq(Refl())) =>
              summon[A =:= B]
            }
          case p: Par[pr, f, fa1, fa2, b1, b2] =>
            fIsNotPair[A, fa1, fa2](ev.flip andThen summon[FB =:= (fa1 ** fa2)])
        }
      })

    override def focusFirst[R](callback: [G[_], X] => (Focus[**, G], F[A] =:= G[F[X]]) => R): R =
      callback[[x] =>> x, A](Focus.id, summon)
  }

  case class Par[**[_, _], F[_], FA1, FA2, A1, A2](
    u1: StripF[**, F, FA1, A1],
    u2: StripF[**, F, FA2, A2],
  ) extends StripF[**, F, FA1 ** FA2, A1 ** A2] {
    override def uniqueOutType[B](that: StripF[**, F, FA1 ** FA2, B])(fIsNotPair: [X, Y, Z] => (F[X] =:= (Y ** Z)) => Nothing)(using
      BiInjective[**],
      Injective[F],
    ): (A1 ** A2) =:= B =
      that.maskInput.visit[(A1 ** A2) =:= B]([FA] => (that: StripF[**, F, FA, B], ev: FA =:= (FA1 ** FA2)) => {
        that match {
          case p: Par[pr, f, fa1, fa2, b1, b2] =>
            (summon[(fa1 ** fa2) =:= FA] andThen ev) match { case BiInjective[**](TypeEq(Refl()), TypeEq(Refl())) =>
              ((u1 uniqueOutType p.u1)(fIsNotPair), (u2 uniqueOutType p.u2)(fIsNotPair))  match { case (TypeEq(Refl()), TypeEq(Refl())) =>
                summon[(A1 ** A2) =:= B]
              }
            }
          case _: Single[pr, f, b] =>
            fIsNotPair[b, FA1, FA2](summon[F[b] =:= FA] andThen ev)
        }
      })

    override def focusFirst[R](callback: [G[_], X] => (Focus[**, G], (FA1 ** FA2) =:= G[F[X]]) => R): R =
      u1.focusFirst[R]([H[_], Y] => (h, ev) =>
        ev match
          case TypeEq(Refl()) =>
            callback[[x] =>> H[x] ** FA2, Y](h.inFst, summon)
      )
  }

  def objectMap[**[_, _], F[_]](fIsNotPair: [X, Y, Z] => (F[X] =:= (Y ** Z)) => Nothing)(using
    BiInjective[**],
    Injective[F],
  ): SemigroupalObjectMap[**, **, StripF[**, F, _, _]] =
    new SemigroupalObjectMap[**, **, StripF[**, F, _, _]] {
      override def uniqueOutputType[A, X, Y](f1: StripF[**, F, A, X], f2: StripF[**, F, A, Y]): X =:= Y =
        (f1 uniqueOutType f2)(fIsNotPair)

      override def pair[A1, A2, X1, X2](f1: StripF[**, F, A1, X1], f2: StripF[**, F, A2, X2]): StripF[**, F, A1 ** A2, X1 ** X2] =
        StripF.Par(f1, f2)

      override def unpair[A1, A2, X](f: StripF[**, F, A1 ** A2, X]): Unpaired[A1, A2, X] =
        f.maskInput.visit[Unpaired[A1, A2, X]]([A] => (u: StripF[**, F, A, X], ev: A =:= (A1 ** A2)) => {
          u match {
            case p: Par[pr, f, a1, a2, x1, x2] =>
              (summon[(a1 ** a2) =:= A] andThen ev) match { case BiInjective[**](TypeEq(Refl()), TypeEq(Refl())) =>
                Unpaired.Impl(p.u1, p.u2)
              }
            case _: Single[pr, f, a] =>
              fIsNotPair[a, A1, A2](summon[F[a] =:= A] andThen ev)
          }
        })
    }
}
