package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, ClampEq, Exists, Monad, NonEmptyList, Validated}
import libretto.lambda.util.Validated.{Valid, invalid}

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

  def traverseFun[->>[_, _], G[_]: Applicative](
    h: [X, Y] => (X --> Y) => G[X ->> Y]
  ): G[CapturingFun[->>, |*|, F, A, B]] =
    this match
      case NoCapture(f)  => h(f).map(NoCapture(_))
      case Closure(x, f) => h(f).map(Closure(x, _))

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

  def leastCommonCapture[-->[_, _], |*|[_, _], F[_], C, A, B](
    fs: NonEmptyList[(C, CapturingFun[-->, |*|, Tupled[|*|, F, _], A, B])],
  )(
    discarderOf: [X] => F[X] => Option[[Y] => DummyImplicit ?=> (X |*| Y) --> Y],
  )(using
    cat: SymmetricSemigroupalCategory[-->, |*|],
    inj: BiInjective[|*|],
    F: ClampEq[F],
  ): Validated[
    (C, NonEmptyList[Exists[F]]),
    CapturingFun[[a, b] =>> NonEmptyList[a --> b], |*|, Tupled[|*|, F, _], A, B]
  ] =
    given sh: Shuffled[[x, y] =>> Either[Elim[|*|, F, x, y], x --> y], |*|] =
      Shuffled[[x, y] =>> Either[Elim[|*|, F, x, y], x --> y], |*|]

    val discarder = new Discarder[-->, |*|, F](discarderOf)

    leastCommonCaptureFree(fs)
      .traverseFun { [x, y] => fs => discarder.foldNel(fs) }

  private def leastCommonCapture[-->[_, _], |*|[_, _], <+>[_, _], F[_], C, A, B](
    fs: Sink[[x, y] =>> (C, CapturingFun[-->, |*|, Tupled[|*|, F,_], x, y]), <+>, A, B],
  )(
    discarderOf: [X] => F[X] => Option[[Y] => DummyImplicit ?=> (X |*| Y) --> Y],
  )(using
    cat: SymmetricSemigroupalCategory[-->, |*|],
    inj: BiInjective[|*|],
    F: ClampEq[F],
  ): Validated[
    (C, NonEmptyList[Exists[F]]),
    Either[
      Sink[-->, <+>, A, B],
      Exists[[X] =>> (Tupled[|*|, F, X], Sink[[a, b] =>> (X |*| a) --> b, <+>, A, B])]
    ]
  ] =
    given sh: Shuffled[[x, y] =>> Either[Elim[|*|, F, x, y], x --> y], |*|] =
      Shuffled[[x, y] =>> Either[Elim[|*|, F, x, y], x --> y], |*|]

    val discarder = new Discarder[-->, |*|, F](discarderOf)

    leastCommonCaptureFree(fs) match
      case Left(fs) =>
        discarder.foldSink[<+>, C, [x] =>> x, A, B](fs).map(Left(_))
      case Right(Exists.Some((x, fs))) =>
        discarder.foldSink(fs).map(fs => Right(Exists((x, fs))))

  private def leastCommonCaptureFree[-->[_, _], |*|[_, _], F[_], C, A, B](
    fs: NonEmptyList[(C, CapturingFun[-->, |*|, Tupled[|*|, F, _], A, B])],
  )(using
    sh: Shuffled[[x, y] =>> Either[Elim[|*|, F, x, y], x --> y], |*|],
    F: ClampEq[F],
  ): CapturingFun[[a, b] =>> NonEmptyList[(C, sh.Shuffled[a, b])], |*|, Tupled[|*|, F, _], A, B] =

    def elim[X](x: Tupled[|*|, F, X]): sh.Shuffled[X |*| B, B] =
      elimFstMany(sh)(x, [a, b] => Left(_))

    val NonEmptyList((c0, f0), tail) = fs
    tail match {
      case Nil =>
        f0.mapFun[[a, b] =>> NonEmptyList[(C, sh.Shuffled[a, b])]]([X, Y] => f => NonEmptyList((c0, sh.lift(Right(f))), Nil))
      case f1 :: fs =>
        (f0, leastCommonCaptureFree(NonEmptyList(f1, fs))) match
          case (NoCapture(f0), NoCapture(fs)) =>
            NoCapture((c0, sh.lift(Right(f0))) :: fs)
          case (NoCapture(f0), Closure(y, fs)) =>
            Closure(y, (c0, sh.lift(Right(f0)).inSnd > elim(y)) :: fs)
          case (Closure(x, f0), NoCapture(fs)) =>
            val p = elim(x)
            Closure(x, (c0, sh.lift(Right(f0))) :: fs.map { case (c, f) => (c, f.inSnd > p) })
          case (Closure(x, f0), Closure(y, fs)) =>
            union(x, y) match
              case Exists.Some((z, p1, p2)) =>
                Closure(z, (c0, sh.fst(p1) > sh.lift(Right(f0))) :: fs.map { case (c, f) => (c, sh.fst(p2) > f) })
    }

  private def leastCommonCaptureFree[-->[_, _], |*|[_, _], <+>[_, _], F[_], C, A, B](
    fs: Sink[[x, y] =>> (C, CapturingFun[-->, |*|, Tupled[|*|, F,_], x, y]), <+>, A, B],
  )(using
    sh: Shuffled[[x, y] =>> Either[Elim[|*|, F, x, y], x --> y], |*|],
    F: ClampEq[F],
  ): Either[
    Sink[[x, y] =>> (C, sh.Shuffled[x, y]), <+>, A, B], // no capture
    Exists[[X] =>> ( // closure
      Tupled[|*|, F, X],
      Sink[[x, y] =>> (C, sh.Shuffled[X |*| x, y]), <+>, A, B]
    )],
  ] =
    def elim[X](x: Tupled[|*|, F, X]): sh.Shuffled[X |*| B, B] =
      elimFstMany(sh)(x, [a, b] => Left(_))

    def thenElim[P, X](
      s: Sink[[x, y] =>> (C, sh.Shuffled[x, y]), <+>, P, B],
      x: Tupled[|*|, F, X],
    ): Sink[[x, y] =>> (C, sh.Shuffled[X |*| x, y]), <+>, P, B] =
      s.map([x] => cf => (cf._1, cf._2.inSnd > elim(x)))

    def afterFst[X, Y, P](
      s: Sink[[a, b] =>> (C, sh.Shuffled[Y |*| a, b]), <+>, P, B],
      f1: sh.Shuffled[X, Y],
    ): Sink[[a, b] =>> (C, sh.Shuffled[X |*| a, b]), <+>, P, B] =
      s.map([x] => cf => (cf._1, f1.inFst > cf._2))

    fs match
      case Sink.Arrow((c, f)) =>
        f match
          case NoCapture(f) =>
            Left(Sink.Arrow((c, sh.lift(Right(f)))))
          case Closure(x, f) =>
            Right(Exists((x, Sink.Arrow((c, sh.lift(Right(f)))))))
      case Sink.Join(s1, s2) =>
        val t1 = leastCommonCaptureFree(s1)
        val t2 = leastCommonCaptureFree(s2)
        (t1, t2) match
          case (Left(t1), Left(t2)) =>
            Left(t1 <+> t2)
          case (Left(t1), Right(Exists.Some((y, t2)))) =>
            Right(Exists((y, thenElim(t1, y) <+> t2)))
          case (Right(Exists.Some((x, t1))), Left(t2)) =>
            Right(Exists((x, t1 <+> thenElim(t2, x))))
          case (Right(Exists.Some((x, t1))), Right(Exists.Some((y, t2)))) =>
            union(x, y) match
              case Exists.Some((z, p1, p2)) =>
                Right(Exists((z, afterFst(t1, p1) <+> afterFst(t2, p2))))

  private class Discarder[-->[_, _], |*|[_, _], F[_]](
    elemDiscarder: [X] => F[X] => Option[[Y] => DummyImplicit ?=> (X |*| Y) --> Y],
  ) {
    def fold[X, Y](g: Either[Elim[|*|, F, X, Y], X --> Y]): Validated[Exists[F], X --> Y] =
      g match
        case Left(Elim.Fst(x1)) =>
          elemDiscarder(x1) match
            case Some(discardFst) => Valid(discardFst[Y])
            case None             => invalid(Exists(x1))
        case Right(g) =>
          Valid(g)

    def foldNel[C, A, B](using
      sh: Shuffled[[x, y] =>> Either[Elim[|*|, F, x, y], x --> y], |*|],
      cat: SymmetricSemigroupalCategory[-->, |*|],
    )(
      fs: NonEmptyList[(C, sh.Shuffled[A, B])]
    ): Validated[
      (C, NonEmptyList[Exists[F]]),
      NonEmptyList[A --> B]
    ] =
      fs.traverse { case (c, f) =>
        f.foldMapA([x, y] => fold[x, y](_))
          .recoverWith(es => invalid((c, es)))
      }


    def foldSink[<+>[_, _], C, G[_], A, B](using
      sh: Shuffled[[x, y] =>> Either[Elim[|*|, F, x, y], x --> y], |*|],
      cat: SymmetricSemigroupalCategory[-->, |*|],
    )(
      fs: Sink[[x, y] =>> (C, sh.Shuffled[G[x], y]), <+>, A, B]
    ): Validated[
      (C, NonEmptyList[Exists[F]]),
      Sink[[x, y] =>> G[x] --> y, <+>, A, B]
    ] =
        fs.traverse { [x] => cf =>
          val (c, f) = cf
          f.foldMapA([x, y] => fold[x, y](_))
            .recoverWith(es => invalid((c, es)))
        }
  }

  private sealed trait Elim[|*|[_, _], F[_], A, B]
  private object Elim {
    case class Fst[|*|[_, _], F[_], A, B](a: F[A]) extends Elim[|*|, F, A |*| B, B]
  }

  private def elimFstMany[|*|[_, _], F[_], X, ->>[_, _], Y](
    sh: Shuffled[->>, |*|],
  )(
    x: Tupled[|*|, F, X],
    inj: [a, b] => Elim[|*|, F, a, b] => (a ->> b),
  ): sh.Shuffled[X |*| Y, Y] =
    x.asBin match {
      case Bin.Leaf(x) =>
        sh.lift(inj(Elim.Fst(x)))
      case Bin.Branch(l, r) =>
        elimFstMany(sh)(Tupled.fromBin(l), inj).inFst > elimFstMany(sh)(Tupled.fromBin(r), inj)
    }

  private def union[-->[_, _], |*|[_, _], F[_], A, B](
    a: Tupled[|*|, F, A],
    b: Tupled[|*|, F, B],
  )(using
    sh: Shuffled[[x, y] =>> Either[Elim[|*|, F, x, y], x --> y], |*|],
    F: ClampEq[F],
  ): Exists[[S] =>> (Tupled[|*|, F, S], sh.Shuffled[S, A], sh.Shuffled[S, B])] = {
    type GArr[X, Y] = Either[Elim[|*|, F, X, Y], X --> Y]

    val discardFst: [X, Y] => F[X] => GArr[X |*| Y, Y] =
      [X, Y] => fx => Left(Elim.Fst(fx))

    (a union b)(discardFst)
  }

  def compileSink[-->[_, _], |*|[_, _], <+>[_, _], F[_], C, A, B](
    fs: Sink[[x, y] =>> (C, CapturingFun[-->, |*|, Tupled[|*|, F,_], x, y]), <+>, A, B],
  )(
    discarderOf: [X] => F[X] => Option[[Y] => DummyImplicit ?=> (X |*| Y) --> Y],
  )(using
    cat: SymmetricSemigroupalCategory[-->, |*|],
    coc: CocartesianSemigroupalCategory[-->, <+>],
    dis: Distribution[-->, |*|, <+>],
    inj: BiInjective[|*|],
    F: ClampEq[F],
  ): Validated[
    (C, NonEmptyList[Exists[F]]),
    CapturingFun[-->, |*|, Tupled[|*|, F, _], A, B]
  ] = {
    import cat.*
    import coc.either
    import dis.distLR

    leastCommonCapture(fs)(discarderOf)
      .map {
        case Left(fs) =>
          NoCapture(fs.reduce([x, y] => either(_, _)))
        case Right(Exists.Some((x, fs))) =>
          Closure(x, fs.reduce([x, y] => (f1, f2) => distLR > either(f1, f2)))
      }
  }
}
