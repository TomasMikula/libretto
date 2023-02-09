package libretto.lambda

import libretto.lambda.util.Zippable

sealed trait CapturingFun[-->[_, _], |*|[_, _], F[_], A, B] {

}

object CapturingFun {
  case class NoCapture[-->[_, _], |*|[_, _], F[_], A, B](f: A --> B) extends CapturingFun[-->, |*|, F, A, B]
  case class Closure[-->[_, _], |*|[_, _], F[_], X, A, B](captured: F[X], f: (X |*| A) --> B) extends CapturingFun[-->, |*|, F, A, B]

  given [-->[_, _], |*|[_, _], F[_]](using
    ev: SymmetricSemigroupalCategory[-->, |*|],
    F: Zippable[|*|, F],
  ): SymmetricSemigroupalCategory[CapturingFun[-->, |*|, F, *, *], |*|] =
    new SymmetricSemigroupalCategory[CapturingFun[-->, |*|, F, *, *], |*|] {
      override def id[A]: CapturingFun[-->, |*|, F, A, A] =
        NoCapture(ev.id[A])

      override def andThen[A, B, C](
        f: CapturingFun[-->, |*|, F, A, B],
        g: CapturingFun[-->, |*|, F, B, C],
      ): CapturingFun[-->, |*|, F, A, C] =
        (f, g) match {
          case (NoCapture(f), NoCapture(g))   => NoCapture(f > g)
          case (NoCapture(f), Closure(x, g))  => Closure(x, ev.snd(f) > g)
          case (Closure(x, f), NoCapture(g))  => Closure(x, f > g)
          case (Closure(x, f), Closure(y, g)) => Closure(F.zip(y, x), ev.assocLR > ev.snd(f) > g)
        }

      override def par[A1, A2, B1, B2](
        f1: CapturingFun[-->, |*|, F, A1, B1],
        f2: CapturingFun[-->, |*|, F, A2, B2],
      ): CapturingFun[-->, |*|, F, A1 |*| A2, B1 |*| B2] =
        (f1, f2) match {
          case (NoCapture(f1), NoCapture(f2))   => NoCapture(ev.par(f1, f2))
          case (NoCapture(f1), Closure(x, f2))  => Closure(x, ev.xi > ev.par(f1, f2))
          case (Closure(x, f1), NoCapture(f2))  => Closure(x, ev.assocRL > ev.par(f1, f2))
          case (Closure(x, f1), Closure(y, f2)) => Closure(F.zip(x, y), ev.ixi > ev.par(f1, f2))
        }

      override def assocLR[A, B, C]: CapturingFun[-->, |*|, F, (A |*| B) |*| C, A |*| (B |*| C)] =
        NoCapture(ev.assocLR)

      override def assocRL[A, B, C]: CapturingFun[-->, |*|, F, A |*| (B |*| C), (A |*| B) |*| C] =
        NoCapture(ev.assocRL)

      override def swap[A, B]: CapturingFun[-->, |*|, F, A |*| B, B |*| A] =
        NoCapture(ev.swap)
    }
}
