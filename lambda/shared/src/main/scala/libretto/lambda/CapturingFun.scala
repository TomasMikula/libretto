package libretto.lambda

import libretto.lambda.util.{Applicative, Exists, Monad, NonEmptyList}

sealed trait CapturingFun[-->[_, _], |*|[_, _], F[_], A, B] {
  import CapturingFun.*

  def mapFun[->>[_, _]](h: [X, Y] => (X --> Y) => (X ->> Y)): CapturingFun[->>, |*|, F, A, B] =
    this match
      case NoCapture(f) => NoCapture(h(f))
      case Closure(captured, f) => Closure(captured, h(f))

  def andThen[C](g: B --> C)(using Semigroupoid[-->]): CapturingFun[-->, |*|, F, A, C] =
    this match
      case NoCapture(f) => NoCapture(f > g)
      case Closure(x, f) => Closure(x, f > g)
}

object CapturingFun {
  case class NoCapture[-->[_, _], |*|[_, _], F[_], A, B](f: A --> B) extends CapturingFun[-->, |*|, F, A, B]
  case class Closure[-->[_, _], |*|[_, _], F[_], X, A, B](captured: F[X], f: (X |*| A) --> B) extends CapturingFun[-->, |*|, F, A, B]

  given [-->[_, _], |*|[_, _], F[_]](using
    ev: SymmetricSemigroupalCategory[-->, |*|],
    F: Zippable[|*|, F],
  ): SymmetricSemigroupalCategory[CapturingFun[-->, |*|, F, _, _], |*|] =
    new SymmetricSemigroupalCategory[CapturingFun[-->, |*|, F, _, _], |*|] {
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

  def leastCommonCapture[-->[_, _], |*|[_, _], F[_], A, B, G[_]](
    f: CapturingFun[-->, |*|, F, A, B],
    g: CapturingFun[-->, |*|, F, A, B],
  )(
    discarderOf: [X] => F[X] => G[[Y] => Unit => (X |*| Y) --> Y],
    union: [X, Y] => (F[X], F[Y]) => G[Exists[[Z] =>> (F[Z], Z --> X, Z --> Y)]],
  )(using
    cat: SemigroupalCategory[-->, |*|],
    G: Applicative[G],
  ): G[CapturingFun[[a, b] =>> (a --> b, a --> b), |*|, F, A, B]] = {
    import cat.fst

    (f, g) match {
      case (NoCapture(f), NoCapture(g)) =>
        G.pure(NoCapture((f, g)))

      case (NoCapture(f), Closure(y, g)) =>
        discarderOf(y)
          .map { discardFst => Closure(y, (discardFst(()) > f, g)) }

      case (Closure(x, f), NoCapture(g)) =>
        discarderOf(x)
          .map { discardFst => Closure(x, (f, discardFst(()) > g)) }

      case (Closure(x, f), Closure(y, g)) =>
        union(x, y)
          .map { case Exists.Some((z, p1, p2)) =>
            Closure(z, (fst(p1) > f, fst(p2) > g))
          }
    }
  }

  def leastCommonCapture[-->[_, _], |*|[_, _], F[_], A, B, G[_]](
    fs: NonEmptyList[CapturingFun[-->, |*|, F, A, B]],
  )(
    discarderOf: [X] => F[X] => G[[Y] => Unit => (X |*| Y) --> Y],
    union: [X, Y] => (F[X], F[Y]) => G[Exists[[Z] =>> (F[Z], Z --> X, Z --> Y)]],
  )(using
    cat: SemigroupalCategory[-->, |*|],
    G: Applicative[G],
    M: Monad[G],
  ):G[CapturingFun[[a, b] =>> NonEmptyList[a --> b], |*|, F, A, B]] =
    leastCommonCapture(fs.head, fs.tail)(discarderOf, union)

  def leastCommonCapture[-->[_, _], |*|[_, _], F[_], X, A, B, G[_]](
    head: CapturingFun[-->, |*|, F, A, B],
    tail: List[CapturingFun[-->, |*|, F, A, B]],
  )(
    discarderOf: [X] => F[X] => G[[Y] => Unit => (X |*| Y) --> Y],
    union: [X, Y] => (F[X], F[Y]) => G[Exists[[Z] =>> (F[Z], Z --> X, Z --> Y)]],
  )(using
    cat: SemigroupalCategory[-->, |*|],
    G: Applicative[G],
    M: Monad[G],
  ): G[CapturingFun[[a, b] =>> NonEmptyList[a --> b], |*|, F, A, B]] = {

    tail match {
      case Nil =>
        G.pure(
          head.mapFun[[a, b] =>> NonEmptyList[a --> b]]([X, Y] => NonEmptyList(_, Nil))
        )
      case f1 :: fs =>
        head match
          case NoCapture(f0) =>
            import Monad.syntax.*
            leastCommonCapture(f1, fs)(discarderOf, union).flatMap {
              case NoCapture(fs) =>
                G.pure(NoCapture(f0 :: fs))
              case Closure(captured, fs) =>
                discarderOf(captured)
                  .map { discardFst => Closure(captured, (discardFst(()) > f0) :: fs) }
            }

          case Closure(captured, f) =>
            leastCommonCapture(captured, tail)(discarderOf, union)
              .map { case Exists.Some((p, Closure(y, fs))) =>
                Closure(y, NonEmptyList(cat.fst(p) > f, fs))
              }
    }
  }

  private def leastCommonCapture[-->[_, _], |*|[_, _], F[_], X, A, B, G[_]](
    acc: F[X],
    fs: List[CapturingFun[-->, |*|, F, A, B]],
  )(
    discarderOf: [X] => F[X] => G[[Y] => Unit => (X |*| Y) --> Y],
    union: [X, Y] => (F[X], F[Y]) => G[Exists[[Z] =>> (F[Z], Z --> X, Z --> Y)]],
  )(using
    cat: SemigroupalCategory[-->, |*|],
    G: Applicative[G],
    M: Monad[G],
  ): G[
    Exists[[Y] =>> (
      Y --> X,
      Closure[[a, b] =>> List[a --> b], |*|, F, Y, A, B]
    )]
  ] = {
    fs match
      case Nil =>
        G.pure(Exists(cat.id[X], Closure(acc, Nil)))
      case f :: fs =>
        f match
          case NoCapture(f) =>
            (discarderOf(acc) zip leastCommonCapture(acc, fs)(discarderOf, union))
              .map { case (discardFst, Exists.Some((p, Closure(y, gs)))) =>
                val g = discardFst(()) > f
                Exists(p, Closure(y, (cat.fst(p) > g) :: gs))
              }

          case Closure(captured, f) =>
            import Monad.syntax.*
            union(acc, captured)
              .flatMap { case Exists.Some((y, p1, p2)) =>
                leastCommonCapture(y, fs)(discarderOf, union)
                  .map { case Exists.Some((q, Closure(z, gs))) =>
                    Exists((q > p1, Closure(z, (cat.fst(q > p2) > f) :: gs)))
                  }
              }
  }
}
