package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, Exists, Monad, NonEmptyList, UniqueTypeArg, Validated}

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
    fs: NonEmptyList[CapturingFun[-->, |*|, Tupled[|*|, F, _], A, B]],
  )(
    discarderOf: [X] => F[X] => G[[Y] => DummyImplicit ?=> (X |*| Y) --> Y],
  )(using
    cat: SymmetricSemigroupalCategory[-->, |*|],
    inj: BiInjective[|*|],
    F: UniqueTypeArg[F],
    G: Applicative[G],
    M: Monad[G],
  ): G[CapturingFun[[a, b] =>> NonEmptyList[a --> b], |*|, Tupled[|*|, F, _], A, B]] =
    leastCommonCapture(fs.head, fs.tail)(new Discarder(discarderOf)/*, union*/)

  private def leastCommonCapture[-->[_, _], |*|[_, _], F[_], X, A, B, G[_]](
    head: CapturingFun[-->, |*|, Tupled[|*|, F, _], A, B],
    tail: List[CapturingFun[-->, |*|, Tupled[|*|, F, _], A, B]],
  )(
    discarder: Discarder[-->, |*|, F, G],
  )(using
    cat: SymmetricSemigroupalCategory[-->, |*|],
    inj: BiInjective[|*|],
    F: UniqueTypeArg[F],
    G: Applicative[G],
    M: Monad[G],
  ): G[CapturingFun[[a, b] =>> NonEmptyList[a --> b], |*|, Tupled[|*|, F, _], A, B]] = {

    tail match {
      case Nil =>
        G.pure(
          head.mapFun[[a, b] =>> NonEmptyList[a --> b]]([X, Y] => NonEmptyList(_, Nil))
        )
      case f1 :: fs =>
        head match
          case NoCapture(f0) =>
            import Monad.syntax.*
            leastCommonCapture(f1, fs)(discarder/*, union*/).flatMap {
              case NoCapture(fs) =>
                G.pure(NoCapture(f0 :: fs))
              case Closure(captured, fs) =>
                discarder.multiDiscard(captured)
                  .map { discardFst => Closure(captured, (f0.inSnd > discardFst[B]) :: fs) }
            }

          case Closure(captured, f) =>
            leastCommonCapture(captured, tail)(discarder)
              .map { case Exists.Some((p, Closure(y, fs))) =>
                Closure(y, NonEmptyList(cat.fst(p) > f, fs))
              }
    }
  }

  private def leastCommonCapture[-->[_, _], |*|[_, _], F[_], X, A, B, G[_]](
    acc: Tupled[|*|, F, X],
    fs: List[CapturingFun[-->, |*|, Tupled[|*|, F, _], A, B]],
  )(
    discarder: Discarder[-->, |*|, F, G],
  )(using
    cat: SymmetricSemigroupalCategory[-->, |*|],
    inj: BiInjective[|*|],
    F: UniqueTypeArg[F],
    G: Applicative[G],
    M: Monad[G],
  ): G[
    Exists[[Y] =>> (
      Y --> X,
      Closure[[a, b] =>> List[a --> b], |*|, Tupled[|*|, F, _], Y, A, B]
    )]
  ] = {
    fs match
      case Nil =>
        G.pure(Exists(cat.id[X], Closure(acc, Nil)))
      case f :: fs =>
        f match
          case NoCapture(f) =>
            (discarder.multiDiscard(acc) zip leastCommonCapture(acc, fs)(discarder/*, union*/))
              .map { case (discardFst, Exists.Some((p, Closure(y, gs)))) =>
                val g = f.inSnd > discardFst[B]
                Exists(p, Closure(y, (cat.fst(p) > g) :: gs))
              }

          case Closure(captured, f) =>
            import Monad.syntax.*
            discarder.union(acc, captured)
              .flatMap { case Exists.Some((y, p1, p2)) =>
                leastCommonCapture(y, fs)(discarder/*, union*/)
                  .map { case Exists.Some((q, Closure(z, gs))) =>
                    Exists((q > p1, Closure(z, (cat.fst(q > p2) > f) :: gs)))
                  }
              }
  }

  private class Discarder[-->[_, _], |*|[_, _], F[_], G[_]](
    elemDiscarder: [X] => F[X] => G[[Y] => DummyImplicit ?=> (X |*| Y) --> Y],
  ) {
    def multiDiscard[A](
      exprs: Tupled[|*|, F, A],
    )(using
      SemigroupalCategory[-->, |*|],
      Applicative[G],
    ): G[[B] => DummyImplicit ?=> (A |*| B) --> B] =
      exprs.asBin match {
        case Bin.Leaf(x) =>
          elemDiscarder(x)
        case Bin.Branch(l, r) =>
          Applicative[G].map2(
            multiDiscard(Tupled.fromBin(l)),
            multiDiscard(Tupled.fromBin(r)),
          ) { (f, g) =>
            [B] => (_: DummyImplicit) ?=> f.apply.inFst > g[B]
          }
      }

    def union[A, B](
      a: Tupled[|*|, F, A],
      b: Tupled[|*|, F, B],
    )(using
      SymmetricSemigroupalCategory[-->, |*|],
      BiInjective[|*|],
      UniqueTypeArg[F],
      Applicative[G],
    ): G[Exists[[S] =>> (Tupled[|*|, F, S], S --> A, S --> B)]] = {
      type GArr[X, Y] = G[X --> Y]
      given shuffledG: Shuffled[GArr, |*|] = Shuffled[GArr, |*|]

      val discardFst: [X, Y] => F[X] => GArr[X |*| Y, Y] =
        [X, Y] => fx => elemDiscarder[X](fx).map(_[Y])

      (a union b)(discardFst) match
        case Exists.Some((p, p1, p2)) =>
          Applicative[G].map2(
            p1.foldMapA[G, -->]([x, y] => (f: G[x --> y]) => f),
            p2.foldMapA[G, -->]([x, y] => (f: G[x --> y]) => f),
          ) { (p1, p2) =>
            Exists((p, p1, p2))
          }
    }
  }

  def compileSink[-->[_, _], |*|[_, _], <+>[_, _], F[_], A, B, G[_]](
    fs: Sink[CapturingFun[-->, |*|, Tupled[|*|, F,_], _, _], <+>, A, B],
  )(
    discarderOf: [X] => F[X] => G[[Y] => DummyImplicit ?=> (X |*| Y) --> Y],
  )(using
    cat: SymmetricSemigroupalCategory[-->, |*|],
    coc: CocartesianSemigroupalCategory[-->, <+>],
    dis: Distribution[-->, |*|, <+>],
    inj: BiInjective[|*|],
    F: UniqueTypeArg[F],
    G: Applicative[G],
    M: Monad[G],
  ): G[CapturingFun[-->, |*|, Tupled[|*|, F,_], A, B]] = {
    import Applicative.*
    import cat.*
    import coc.either
    import dis.distLR

    val discarder = new Discarder[-->, |*|, F, G](discarderOf)

    fs.reduceM[G](
      [x, y] => (
        f1: CapturingFun[-->, |*|, Tupled[|*|, F,_], x, B],
        f2: CapturingFun[-->, |*|, Tupled[|*|, F,_], y, B],
      ) => {
        (f1, f2) match {
          case (NoCapture(f1), NoCapture(f2)) =>
            NoCapture(coc.either(f1, f2)).pure
          case (Closure(x, f1), NoCapture(f2)) =>
            discarder.multiDiscard(x).map :
              discardFst => Closure(x, distLR > either(f1, discardFst.apply > f2))
          case (NoCapture(f1), Closure(y, f2)) =>
            discarder.multiDiscard(y).map :
              discardFst => Closure(y, distLR > either(discardFst.apply > f1, f2))
          case (Closure(x, f1), Closure(y, f2)) =>
            discarder.union(x, y)
              .map { case Exists.Some((p, p1, p2)) =>
                Closure(p, distLR > either(p1.inFst > f1, p2.inFst > f2))
              }
        }
      }
    )
  }
}
