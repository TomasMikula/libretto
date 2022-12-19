package libretto.lambda

import libretto.util.BiInjective

class Shuffled[->[_, _], |*|[_, _]](using BiInjective[|*|]) {
  val shuffle = new Shuffle[|*|]
  import shuffle.{~⚬, Transfer, TransferOpt}

  sealed trait Shuffled[A, B] {
    def after[Z](that: Shuffled[Z, A]): Shuffled[Z, B]
    def thenShuffle[C](that: B ~⚬ C): Shuffled[A, C]
    def afterShuffle[Z](that: Z ~⚬ A): Shuffled[Z, B]
    def fold(using SymmetricSemigroupalCategory[->, |*|]): A -> B
    def inFst[Y]: Shuffled[A |*| Y, B |*| Y]
    def inSnd[X]: Shuffled[X |*| A, X |*| B]
    def unconsSome: UnconsSomeRes[A, B]

    def >[C](that: Shuffled[B, C]): Shuffled[A, C] =
      that after this

    def at[F[_]](f: Focus[|*|, F]): Shuffled[F[A], F[B]] =
      f match {
        case Focus.Id()    => this
        case Focus.Fst(f1) => this.at(f1).inFst
        case Focus.Snd(f2) => this.at(f2).inSnd
      }

    def chaseFw[F[_], X](i: Focus[|*|, F])(using A =:= F[X]): ChaseFwRes[F, X, B]

    def chaseBw[G[_], X](i: Focus[|*|, G])(using B =:= G[X]): ChaseBwRes[A, G, X]

    def project[C](
      p: Projection[|*|, B, C],
      f: [X, Y, Z] => (X -> Y, Projection[|*|, Y, Z]) => Shuffled[X, Z],
    ): ProjectRes[A, C] = ???

    def to[C](using ev: B =:= C): Shuffled[A, C] =
      ev.substituteCo(this)

    def from[Z](using ev: Z =:= A): Shuffled[Z, B] =
      ev.substituteContra[Shuffled[*, B]](this)
  }

  sealed trait Permeable[A, B] extends Shuffled[A, B]

  case class Impermeable[A, X, Y, B](l: A ~⚬ X, m: Plated[X, Y], r: Y ~⚬ B) extends Shuffled[A, B] {
    override def after[Z](that: Shuffled[Z, A]): Shuffled[Z, B] =
      (that thenShuffle l) match {
        case Impermeable(i, j, k) => Impermeable(i, Plated.Sandwich(j, k, m), r)
        case k: Permeable[Z, X] => (m after k) match {
          case Plated.Preshuffled(k, m) => Impermeable(k, m, r)
        }
      }

    override def thenShuffle[C](s: B ~⚬ C): Impermeable[A, X, Y, C] =
      Impermeable(l, m, r > s)

    override def afterShuffle[Z](k: Z ~⚬ A): Shuffled[Z, B] =
      Impermeable(k > l, m, r)

    override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B = {
      val (f, g, h) = (l.fold, m.fold, r.fold)
      ev.andThen(f, ev.andThen(g, h))
    }

    override def inFst[Q]: Shuffled[A |*| Q, B |*| Q] =
      swap > inSnd[Q] > swap

    override def inSnd[P]: Shuffled[P |*| A, P |*| B] =
      SemiObstructed(~⚬.snd(l), m, r, TransferOpt.None())

    override def unconsSome: UnconsSomeRes[A, B] =
      m.unconsSome match
        case c: Plated.UnconsSomeRes.Cons[f, v, w, y] =>
          UnconsSomeRes.Cons[A, f, v, w, B](l, c.i, c.f, c.post thenShuffle r)

    override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: B =:= G[T]): ChaseBwRes[A, G, T] =
      r.chaseBw(i) match
        case tr: ~⚬.ChaseBwRes.Transported[y, f, g, t] =>
          m.chaseBw[f, T](tr.f)(using tr.ev) match
            case o: Plated.ChaseBwRes.OriginatesFrom[x, f0, v, w, t0, g0] =>
              ChaseBwRes.OriginatesFrom(Pure(l) > o.pre, o.i, o.f, o.w, o.post > Pure(tr.s[T](())))
        case ~⚬.ChaseBwRes.Split(ev) =>
          ChaseBwRes.Split(ev)

    override def chaseFw[F[_], T](i: Focus[|*|, F])(using A =:= F[T]): ChaseFwRes[F, T, B] =
      l.chaseFw(i) match
        case tr: ~⚬.ChaseFwRes.Transported[f, t, g, x] =>
          ???
        case ~⚬.ChaseFwRes.Split(ev) =>
          ChaseFwRes.Split(ev)
  }

  case class Pure[A, B](s: A ~⚬ B) extends Permeable[A, B] {
    override def after[Z](that: Shuffled[Z, A]): Shuffled[Z, B] =
      that thenShuffle s

    override def thenShuffle[C](t: B ~⚬ C): Pure[A, C] =
      Pure(s > t)

    override def afterShuffle[Z](r: Z ~⚬ A): Shuffled[Z, B] =
      Pure(r > s)

    override def fold(using SymmetricSemigroupalCategory[->, |*|]): A -> B =
      s.fold

    override def inFst[Y]: Shuffled[A |*| Y, B |*| Y] =
      Pure(~⚬.fst(s))

    override def inSnd[X]: Shuffled[X |*| A, X |*| B] =
      Pure(~⚬.snd(s))

    override def unconsSome: UnconsSomeRes[A, B] =
      UnconsSomeRes.Pure(s)

    override def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: B =:= G[X]): ChaseBwRes[A, G, X] =
      s.chaseBw(i) match
        case tr: ~⚬.ChaseBwRes.Transported[a, f, g, x] =>
          ChaseBwRes.Transported(tr.ev, tr.f, [x] => (_: Unit) => Pure(tr.s[x](())))
        case ~⚬.ChaseBwRes.Split(ev) =>
          ChaseBwRes.Split(ev)

    override def chaseFw[F[_], X](i: Focus[|*|, F])(using A =:= F[X]): ChaseFwRes[F, X, B] =
      s.chaseFw(i) match
        case tr: ~⚬.ChaseFwRes.Transported[f, x, g, b] =>
          ChaseFwRes.Transported([x] => (_: Unit) => Pure(tr.s[x](())), tr.g, tr.ev)
        case ~⚬.ChaseFwRes.Split(ev) =>
          ChaseFwRes.Split(ev)
  }

  case class SemiObstructed[A, X1, X2, Y2, Z2, B1, B2](
    left    : A ~⚬ (X1 |*| X2),
    bottom1 : Plated[X2, Y2],
    bottom2 : Y2 ~⚬ Z2,
    right   : TransferOpt[X1, Z2, B1, B2],
  ) extends Permeable[A, B1 |*| B2] {
    override def after[Z](that: Shuffled[Z, A]): Shuffled[Z, B1 |*| B2] =
      that match {
        case Pure(s) =>
          SemiObstructed(s > left, bottom1, bottom2, right)
        case Impermeable(l, m, r) =>
          ~⚬.decompose1((r > left).invert) match {
            case ~⚬.Decomposition1(f1, f2, g, ev) =>
              val m1 = Plated.SemiSnoc(ev.flip.substituteCo(m), RevTransferOpt(g), f2.invert, bottom1)
              Impermeable(l, m1, ~⚬.par(f1.invert, bottom2) > right.asShuffle)
          }
        case SemiObstructed(l, b1, b2, r) =>
          ▄░▄(b1, ~⚬.snd(b2) > r.asShuffle > left, bottom1)
            .afterShuffle(l)
            .thenShuffle(~⚬.snd(bottom2) > right.asShuffle)
      }

    override def thenShuffle[C](s: (B1 |*| B2) ~⚬ C): Permeable[A, C] =
      ~⚬.decompose1(right.asShuffle > s) match {
        case ~⚬.Decomposition1(g1, g2, h, ev) => ev.substituteCo[Permeable[A, *]](SemiObstructed(left > ~⚬.fst(g1), bottom1, bottom2 > g2, h))
      }

    override def afterShuffle[Z](that: Z ~⚬ A): Shuffled[Z, B1 |*| B2] =
      SemiObstructed(that > left, bottom1, bottom2, right)

    override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> (B1 |*| B2) = {
      val (f, g, h, i) = (left.fold, bottom1.fold, bottom2.fold, right.fold)
      ev.andThen(f, ev.andThen(ev.snd(ev.andThen(g, h)), i))
    }

    override def inFst[Q]: Shuffled[A |*| Q, (B1 |*| B2) |*| Q] =
      swap > inSnd[Q] > swap

    override def inSnd[P]: Shuffled[P |*| A, P |*| (B1 |*| B2)] =
      ~⚬.decompose[P |*| X1, Y2, P, B1 |*| B2](~⚬.snd(bottom2) > ~⚬.assocLR > ~⚬.snd(right.asShuffle)) match {
        case ~⚬.Decomposition(f1, f2, h) =>
          SemiObstructed(~⚬.snd(left) > ~⚬.assocRL > ~⚬.fst(f1), bottom1, f2, h)
      }

    override def unconsSome: UnconsSomeRes[A, B1 |*| B2] =
      bottom1.unconsSome match
        case c: Plated.UnconsSomeRes.Cons[f, x, y, y2] =>
          UnconsSomeRes.Cons[A, [t] =>> X1 |*| f[t], x, y, B1 |*| B2](
            left,
            Focus.snd(c.i),
            c.f,
            (c.post thenShuffle bottom2).inSnd thenShuffle right.asShuffle,
          )

    override def chaseFw[F[_], T](i: Focus[|*|, F])(using A =:= F[T]): ChaseFwRes[F, T, B1 |*| B2] = {
      left.chaseFw(i) match
        case ~⚬.ChaseFwRes.Split(ev) =>
          ChaseFwRes.Split(ev)
        case tr: ~⚬.ChaseFwRes.Transported[f, t, g, x] =>
          tr.g match
            case Focus.Id() =>
              ChaseFwRes.Split(tr.ev)
            case Focus.Fst(_) =>
              UnhandledCase.raise(s"${tr.g}")
            case snd: Focus.Snd[pair, g2, p] =>
              val BiInjective[|*|](x1p, x2g2t) = tr.ev.flip andThen summon[g[T] =:= (p |*| g2[T])]
              bottom1.chaseFw[g2, T](snd.i)(using x2g2t) match
                case Plated.ChaseFwRes.Split(ev) =>
                  ChaseFwRes.Split(ev)
                case r: Plated.ChaseFwRes.FedTo[g2, t, v, w, h, y2] =>
                  ChaseFwRes.FedTo[F, T, v, w, [t] =>> X1 |*| h[t], B1 |*| B2](
                    Pure(tr.s[T](())) > par(id(x1p.flip), r.pre),
                    r.v,
                    r.f,
                    r.g.inSnd[X1],
                    (r.post thenShuffle bottom2).inSnd[X1] thenShuffle right.asShuffle,
                  )
    }

    override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[T]): ChaseBwRes[A, G, T] =
      right.asShuffle.chaseBw(i) match
        case ~⚬.ChaseBwRes.Split(ev) =>
          ChaseBwRes.Split(ev)
        case tr: ~⚬.ChaseBwRes.Transported[a, f, g, t] =>
          ???
          // summon[g[T] =:= (B1 |*| B2)]
          // def go[F[_], G[_]](f: Focus[|*|, F], s: [t] => Unit => F[t] ~⚬ G[t], g: Focus[|*|, G]): ChaseBwRes[A, G[T], T] =
          //   f match
          //     case Focus.Id() =>
          //       summon[F[T] =:= T]
          //       summon[F[T] =:= (X1 |*| Z2)]
          //       ChaseBwRes.Split(summon[T =:= (X1 |*| Z2)])
          //     case Focus.Fst(k) =>
          //       left.chaseBw(Inj.fst(k.at[T])) match
          //         case ~⚬.ChaseBwRes.Split(ev) =>
          //           ChaseBwRes.Split(ev)
          //         case ltr: ~⚬.ChaseBwRes.Transported[lf, lg, lt] =>
          //           ChaseBwRes.Transported(ltr.at[T])
          //     case Inj.Snd(k) =>
          //       ???
          // tr.f match
          //   case Focus.Id() =>
          //     summon[f[T] =:= T]
          //     summon[f[T] =:= (X1 |*| Z2)]
          //     ChaseBwRes.Split(summon[T =:= (X1 |*| Z2)])
          //   case Focus.Fst(k) =>
          //     left.chaseBw(Inj.fst(k.at[T])) match
          //       case ~⚬.ChaseBwRes.Split(ev) =>
          //         ChaseBwRes.Split(ev)
          //       case ltr: ~⚬.ChaseBwRes.Transported[lf, lg, lt] =>
          //         ChaseBwRes.Transported(ltr.at[T])
          //   case Inj.Snd(k) =>
          //     ???
  }

  object Permeable {
    def id[X]: Permeable[X, X] =
      Pure(~⚬.Id())
  }

  sealed trait Plated[A, B] {
    import Plated._

    def after[Z](that: Permeable[Z, A]): Plated.Preshuffled[Z, ?, B] =
      that match {
        case Pure(s) =>
          Preshuffled(s, this)
        case SemiObstructed(l, b1, b2, r) =>
          Preshuffled(l, SemiCons(b1, b2, r, this))
      }

    def asShuffled: Shuffled[A, B] =
      Impermeable(~⚬.id, this, ~⚬.id)

    def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B

    def unconsSome: Plated.UnconsSomeRes[A, B]

    def chaseFw[F[_], X](i: Focus[|*|, F])(using A =:= F[X]): Plated.ChaseFwRes[F, X, B]
    def chaseBw[G[_], X](i: Focus[|*|, G])(using B =:= G[X]): Plated.ChaseBwRes[A, G, X]
  }

  object Plated {
    case class Solid[A, B](f: A -> B) extends Plated[A, B] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B =
        f

      override def unconsSome: UnconsSomeRes[A, B] =
        UnconsSomeRes.Cons(Focus.id, f, id)

      override def chaseFw[F[_], X](i: Focus[|*|, F])(using ev: A =:= F[X]): ChaseFwRes[F, X, B] =
        ChaseFwRes.FedTo[F, X, F, B, [x] =>> x, B](id[F[X]], i, ev.substituteCo[[x] =>> x -> B](f), Focus.id, id[B])

      override def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: B =:= G[X]): ChaseBwRes[A, G, X] =
        ChaseBwRes.OriginatesFrom[A, [x] =>> x, A, G, X, G](id[A], Focus.id, ev.substituteCo(f), i, id[G[X]])
    }

    case class Stacked[A1, A2, B1, B2](f1: Plated[A1, B1], f2: Plated[A2, B2]) extends Plated[A1 |*| A2, B1 |*| B2] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> (B1 |*| B2) =
        ev.par(f1.fold, f2.fold)

      override def unconsSome: UnconsSomeRes[A1 |*| A2, B1 |*| B2] =
        f1.unconsSome match
          case c: UnconsSomeRes.Cons[f, x, y, b1] =>
            UnconsSomeRes.Cons[[t] =>> f[t] |*| A2, x, y, B1 |*| B2](c.i.inFst[A2], c.f, par(c.post, f2.asShuffled))

      override def chaseFw[F[_], X](i: Focus[|*|, F])(using (A1 |*| A2) =:= F[X]): ChaseFwRes[F, X, B1 |*| B2] =
        ???

      override def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[X]): ChaseBwRes[A1 |*| A2, G, X] =
        // i match
        //   case Inj.Id()   => ChaseBwRes.Split(summon[X =:= (B1 |*| B2)])
        //   case Inj.Fst(j) => f1.chaseBw(j).inFst(f2.asShuffled)
        //   case Inj.Snd(j) => f2.chaseBw(j).inSnd(f1.asShuffled)
        ???
    }

    case class Sandwich[A, X, Y, B](l: Plated[A, X], m: X ~⚬ Y, r: Plated[Y, B]) extends Plated[A, B] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B =
        ev.andThen(l.fold, ev.andThen(m.fold, r.fold))

      override def unconsSome: UnconsSomeRes[A, B] =
        l.unconsSome match
          case c: UnconsSomeRes.Cons[f, v, w, x] =>
            UnconsSomeRes.Cons(c.i, c.f, (c.post thenShuffle m) > r.asShuffled)

      override def chaseFw[F[_], X](i: Focus[|*|, F])(using A =:= F[X]): ChaseFwRes[F, X, B] =
        l.chaseFw(i) andThen (Pure(m) > r.asShuffled)

      override def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: B =:= G[X]): ChaseBwRes[A, G, X] =
        r.chaseBw(i) after (l.asShuffled thenShuffle m)
    }

    case class SemiCons[A1, A2, X2, Y2, Z1, Z2, B](
      semiHead: Plated[A2, X2],
      s: X2 ~⚬ Y2,
      t: TransferOpt[A1, Y2, Z1, Z2],
      tail: Plated[Z1 |*| Z2, B],
    ) extends Plated[A1 |*| A2, B] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> B =
        ev.andThen(ev.andThen(ev.snd(ev.andThen(semiHead.fold, s.fold)), t.fold), tail.fold)

      override def unconsSome: UnconsSomeRes[A1 |*| A2, B] =
        semiHead.unconsSome match
          case c: UnconsSomeRes.Cons[f, v, w, x2] =>
            UnconsSomeRes.Cons[[t] =>> A1 |*| f[t], v, w, B](
              c.i.inSnd,
              c.f,
              ((c.post thenShuffle s).inSnd thenShuffle t.asShuffle) > tail.asShuffled,
            )

      override def chaseFw[F[_], X](i: Focus[|*|, F])(using (A1 |*| A2) =:= F[X]): ChaseFwRes[F, X, B] = ???

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: B =:= G[T]): ChaseBwRes[A1 |*| A2, G, T] =
        tail.chaseBw(i) after (semiHead.asShuffled thenShuffle s).inSnd[A1].thenShuffle(t.asShuffle)
    }

    case class SemiSnoc[A, X1, X2, Y2, Z2, B1, B2](
      init: Plated[A, X1 |*| X2],
      t: RevTransferOpt[X1, X2, B1, Y2],
      s: Y2 ~⚬ Z2,
      semiLast: Plated[Z2, B2],
    ) extends Plated[A, B1 |*| B2] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> (B1 |*| B2) =
        ev.andThen(init.fold, ev.andThen(t.fold, ev.snd(ev.andThen(s.fold, semiLast.fold))))

      override def unconsSome: UnconsSomeRes[A, B1 |*| B2] =
        init.unconsSome match
          case c: UnconsSomeRes.Cons[f, v, w, x1x2] =>
            UnconsSomeRes.Cons(c.i, c.f, (c.post thenShuffle t.asShuffle) > (Pure(s) > semiLast.asShuffled).inSnd)

      override def chaseFw[F[_], X](i: Focus[|*|, F])(using A =:= F[X]): ChaseFwRes[F, X, B1 |*| B2] = ???

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[T]): ChaseBwRes[A, G, T] =
        i match
          case Focus.Id() =>
            ChaseBwRes.Split((ev andThen summon[G[T] =:= T]).flip)
          case j: Focus.Fst[p, f, b] =>
            val BiInjective[|*|](b1ft, b2b) = ev andThen summon[G[T] =:= (f[T] |*| b)]
            import shuffle.zip
            t.asShuffle.chaseBw[[t] =>> f[t] |*| Y2, T](j.i.inFst)(using b1ft zip summon[Y2 =:= Y2]) match
              case ~⚬.ChaseBwRes.Split(ev) =>
                ChaseBwRes.Split(ev)
              case r: ~⚬.ChaseBwRes.Transported[a, f1, g1, t] =>
                def go[F[_]](ev1: (X1 |*| X2) =:= F[T], f: Focus[|*|, F], s1: [t] => Unit => F[t] ~⚬ (f[t] |*| Y2)): ChaseBwRes[A, G, T] =
                  init.chaseBw[F, T](f)(using ev1) match
                    case ChaseBwRes.Split(ev) =>
                      ChaseBwRes.Split(ev)
                    case ChaseBwRes.OriginatesFrom(pre, i1, f, i2, post) =>
                      ChaseBwRes.OriginatesFrom(pre, i1, f, i2, (post thenShuffle (s1[T](()) > ~⚬.snd(s))) > semiLast.asShuffled.to[b](using b2b).inSnd[f[T]])
                go[f1](r.ev, r.f, r.s)
          case j: Focus.Snd[pair, g2, b1] =>
            val BiInjective[|*|](ev1, ev2) = ev
            ev1.substituteCo[[b1] =>> ChaseBwRes[A, [t] =>> b1 |*| g2[t], T]](
              semiLast.chaseBw[g2, T](j.i)(using ev2)
                .after(Pure(s))
                .inSnd[B1]
                .after(init.asShuffled > Pure(t.asShuffle))
            )
    }

    case class XI[A1, A2, P1, P2, Q, R, S1, S2, B1, B2](
      l: Plated[A2, P1 |*| P2],
      lt: RevTransferOpt[P1, P2, B1, Q],
      b: Q ~⚬ R,
      rt: TransferOpt[A1, R, S1, S2],
      r: Plated[S1 |*| S2, B2],
    ) extends Plated[A1 |*| A2, B1 |*| B2] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> (B1 |*| B2) = {
        import ev.andThen
        andThen(
          ev.snd(andThen(l.fold, andThen(lt.fold, ev.snd(b.fold)))),
          andThen(
            ev.xi,
            ev.snd(andThen(rt.fold, r.fold)),
          ),
        )
      }

      override def unconsSome: UnconsSomeRes[A1 |*| A2, B1 |*| B2] =
        l.unconsSome match
          case c: UnconsSomeRes.Cons[f, x, y, p1p2] =>
            UnconsSomeRes.Cons[[t] =>> A1 |*| f[t], x, y, B1 |*| B2](
              c.i.inSnd,
              c.f,
              ((c.post thenShuffle (lt.asShuffle > ~⚬.snd(b))).inSnd[A1] thenShuffle ~⚬.xi) > (Pure(rt.asShuffle) > r.asShuffled).inSnd,
            )

      override def chaseFw[F[_], X](i: Focus[|*|, F])(using (A1 |*| A2) =:= F[X]): ChaseFwRes[F, X, B1 |*| B2] = ???

      override def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[X]): ChaseBwRes[A1 |*| A2, G, X] =
        ???
    }

    case class Preshuffled[A, X, B](s: A ~⚬ X, t: Plated[X, B])

    enum UnconsSomeRes[A, B] {
      case Cons[F[_], X, Y, B](
        i: Focus[|*|, F],
        f: X -> Y,
        post: Shuffled[F[Y], B],
      ) extends UnconsSomeRes[F[X], B]
    }

    sealed trait ChaseFwRes[F[_], X, B] {
      def andThen[C](that: Shuffled[B, C]): ChaseFwRes[F, X, C]
    }

    object ChaseFwRes {
      case class FedTo[F[_], X, V[_], W, G[_], B](
        pre: Shuffled[F[X], G[V[X]]],
        v: Focus[|*|, V],
        f: V[X] -> W,
        g: Focus[|*|, G],
        post: Shuffled[G[W], B],
      ) extends ChaseFwRes[F, X, B] {
        override def andThen[C](that: Shuffled[B, C]): ChaseFwRes[F, X, C] =
          FedTo(pre, v, f, g, post > that)
      }

      case class Split[F[_], X, X1, X2, B](ev: X =:= (X1 |*| X2)) extends ChaseFwRes[F, X, B] {
        override def andThen[C](that: Shuffled[B, C]): ChaseFwRes[F, X, C] = Split(ev)
      }
    }

    sealed trait ChaseBwRes[A, G[_], X] {
      def after[P](p: Shuffled[P, A]): ChaseBwRes[P, G, X]
      def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes[A |*| P, [x] =>> G[x] |*| Q, X]
      def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes[P |*| A, [x] =>> Q |*| G[x], X]

      def inFst[Q]: ChaseBwRes[A |*| Q, [x] =>> G[x] |*| Q, X] = inFst(id[Q])
      def inSnd[P]: ChaseBwRes[P |*| A, [x] =>> P |*| G[x], X] = inSnd(id[P])
    }

    object ChaseBwRes {
      case class OriginatesFrom[A, F[_], V, W[_], X, G[_]](
        pre: Shuffled[A, F[V]],
        i: Focus[|*|, F],
        f: V -> W[X],
        w: Focus[|*|, W],
        post: Shuffled[F[W[X]], G[X]],
      ) extends ChaseBwRes[A, G, X] {
        override def after[P](p: Shuffled[P, A]): ChaseBwRes[P, G, X] =
          OriginatesFrom(p > pre, i, f, w, post)

        override def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes[A |*| P, [x] =>> G[x] |*| Q, X] =
          OriginatesFrom[A |*| P, [t] =>> F[t] |*| Q, V, W, X, [x] =>> G[x] |*| Q](par(pre, snd), i.inFst, f, w, post.inFst)

        override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes[P |*| A, [x] =>> Q |*| G[x], X] =
          OriginatesFrom[P |*| A, [t] =>> Q |*| F[t], V, W, X, [x] =>> Q |*| G[x]](par(fst, pre), i.inSnd, f, w, post.inSnd)
      }

      case class Split[A, G[_], X, X1, X2](ev: X =:= (X1 |*| X2)) extends ChaseBwRes[A, G, X] {
        override def after[P](p: Shuffled[P, A]): ChaseBwRes[P, G, X] = Split(ev)
        override def inFst[P, Q](snd: Shuffled[P, Q]): ChaseBwRes[A |*| P, [x] =>> G[x] |*| Q, X] = Split(ev)
        override def inSnd[P, Q](fst: Shuffled[P, Q]): ChaseBwRes[P |*| A, [x] =>> Q |*| G[x], X] = Split(ev)
      }
    }
  }
  import Plated._

  case class RevTransferOpt[A1, A2, B1, B2](t: TransferOpt[B1, B2, A1, A2]) {
    def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> (B1 |*| B2) =
      this.asShuffle.fold

    def asShuffle: (A1 |*| A2) ~⚬ (B1 |*| B2) =
      t.asShuffle.invert
  }

  def id[X]: Shuffled[X, X] =
    Permeable.id

  def id[X, Y](implicit ev: X =:= Y): Shuffled[X, Y] =
    ev.substituteCo(Permeable.id[X])

  def pure[X, Y](f: X ~⚬ Y): Shuffled[X, Y] =
    Pure(f)

  def fst[X, Y, Z](f: Shuffled[X, Y]): Shuffled[X |*| Z, Y |*| Z] =
    f.inFst[Z]

  def snd[X, Y, Z](f: Shuffled[Y, Z]): Shuffled[X |*| Y, X |*| Z] =
    f.inSnd[X]

  def par[X1, X2, Y1, Y2](f1: Shuffled[X1, Y1], f2: Shuffled[X2, Y2]): Shuffled[X1 |*| X2, Y1 |*| Y2] =
    fst(f1) > snd(f2)

  def assocLR[X, Y, Z]: Shuffled[(X |*| Y) |*| Z, X |*| (Y |*| Z)] =
    Pure(~⚬.assocLR)

  def assocRL[X, Y, Z]: Shuffled[X |*| (Y |*| Z), (X |*| Y) |*| Z] =
    Pure(~⚬.assocRL)

  def swap[X, Y]: Shuffled[X |*| Y, Y |*| X] =
    Pure(~⚬.swap)

  def ix[X, Y, Z]: Shuffled[(X |*| Y) |*| Z, (X |*| Z) |*| Y] =
    Pure(~⚬.ix)

  def xi[X, Y, Z]: Shuffled[X |*| (Y |*| Z), Y |*| (X |*| Z)] =
    Pure(~⚬.xi)

  def ixi[W, X, Y, Z]: Shuffled[(W |*| X) |*| (Y |*| Z), (W |*| Y) |*| (X |*| Z)] =
    Pure(~⚬.ixi)

  def lift[X, Y](f: X -> Y): Shuffled[X, Y] =
    Impermeable(~⚬.id, Solid(f), ~⚬.id)

  def extractSnd[F[_], X, Y](i: Focus[|*|, F]): Shuffled[F[X |*| Y], F[X] |*| Y] =
    i match {
      case Focus.Id()    => id[X |*| Y]
      case Focus.Fst(i1) => extractSnd(i1).inFst > ix
      case Focus.Snd(i2) => extractSnd(i2).inSnd > assocRL
    }

  def absorbSnd[F[_], X, Y](i: Focus[|*|, F]): Shuffled[F[X] |*| Y, F[X |*| Y]] =
    i match {
      case Focus.Id()    => id[X |*| Y]
      case Focus.Fst(i1) => ix > fst(absorbSnd(i1))
      case Focus.Snd(i2) => assocLR > snd(absorbSnd(i2))
    }

  private def ▄░▄[A1, A2, X2, Y2, B1, B2](
    l: Plated[A2, X2],
    m: (A1 |*| X2) ~⚬ (B1 |*| Y2),
    r: Plated[Y2, B2],
  ): Shuffled[A1 |*| A2, B1 |*| B2] =
    ~⚬.tryUntangle(m) match {
      case Right((m1, m2)) =>
        SemiObstructed(
          ~⚬.fst(m1),
          Plated.Sandwich(l, m2, r),
          ~⚬.id,
          TransferOpt.None(),
        )
      case Left(~⚬.Xfer(f1, f2, g)) =>
        Tr(g).`▄░_this_▄`(l, f1, f2, r)
    }

  /** Wrapper of [[Transfer]] to add additional virtual methods. */
  private sealed trait Tr[P1, P2, Q1, Q2] {
    def `▄░_this_▄`[A1, A2, X2, Z2](
      l: Plated[A2, X2],
      f1: A1 ~⚬ P1,
      f2: X2 ~⚬ P2,
      r: Plated[Q2, Z2],
    ): Shuffled[A1 |*| A2, Q1 |*| Z2]
  }

  private object Tr {
    case class Swap[P1, P2](value: Transfer.Swap[P1, P2]) extends Tr[P1, P2, P2, P1] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ P1,
        f2: X2 ~⚬ P2,
        r: Plated[P1, Z2],
      ): Shuffled[A1 |*| A2, P2 |*| Z2] =
        Impermeable(
          ~⚬.fst(f1),
          Plated.Stacked(r, l),
          ~⚬.snd(f2) > ~⚬.swap,
        )

    }

    case class AssocLR[P1, P2, P3, Q2, Q3](value: Transfer.AssocLR[P1, P2, P3, Q2, Q3]) extends Tr[P1 |*| P2, P3, P1, Q2 |*| Q3] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ (P1 |*| P2),
        f2: X2 ~⚬ P3,
        r: Plated[Q2 |*| Q3, Z2],
      ): Shuffled[A1 |*| A2, P1 |*| Z2] =
        SemiObstructed(
          ~⚬.fst(f1) > ~⚬.assocLR,
          Plated.SemiCons(l, f2, value.g, r),
          ~⚬.id,
          TransferOpt.None(),
        )

    }

    case class AssocRL[P1, P2, P3, Q1, Q2](value: Transfer.AssocRL[P1, P2, P3, Q1, Q2]) extends Tr[P1, P2 |*| P3, Q1 |*| Q2, P3] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ P1,
        f2: X2 ~⚬ (P2 |*| P3),
        r: Plated[P3, Z2],
      ): Shuffled[A1 |*| A2, (Q1 |*| Q2) |*| Z2] =
        revDecompose1(f2) match {
          case RevDecomposition1(ev, t, g1, g2) =>
            SemiObstructed(
              ~⚬.fst(f1),
              Plated.SemiSnoc(ev.substituteCo(l), t, g2, r),
              ~⚬.fst(g1),
              Transfer.AssocRL(value.g),
            )
        }

    }

    case class IX[P1, P2, P3, Q1, Q2](value: Transfer.IX[P1, P2, P3, Q1, Q2]) extends Tr[P1 |*| P2, P3, Q1 |*| Q2, P2] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ (P1 |*| P2),
        f2: X2 ~⚬ P3,
        r: Plated[P2, Z2],
      ): Shuffled[A1 |*| A2, (Q1 |*| Q2) |*| Z2] =
        Pure(~⚬.fst(f1) > ~⚬.assocLR) >
          snd(Impermeable(~⚬.swap, Plated.Stacked(l, r), ~⚬.fst(f2))) >
          Pure(~⚬.assocRL > ~⚬.fst(value.g.asShuffle))

    }

    case class XI[P1, P2, P3, Q2, Q3](value: Transfer.XI[P1, P2, P3, Q2, Q3]) extends Tr[P1, P2 |*| P3, P2, Q2 |*| Q3] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ P1,
        f2: X2 ~⚬ (P2 |*| P3),
        r: Plated[Q2 |*| Q3, Z2],
      ): Shuffled[A1 |*| A2, P2 |*| Z2] =
        revDecompose1(f2) match {
          case RevDecomposition1(ev, g, h1, h2) =>
            Impermeable(~⚬.fst(f1), Plated.XI(ev.substituteCo(l), g, h2, value.g, r), ~⚬.fst(h1))
        }

    }

    case class IXI[P1, P2, P3, P4, Q1, Q2, Q3, Q4](value: Transfer.IXI[P1, P2, P3, P4, Q1, Q2, Q3, Q4]) extends Tr[P1 |*| P2, P3 |*| P4, Q1 |*| Q2, Q3 |*| Q4] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ (P1 |*| P2),
        f2: X2 ~⚬ (P3 |*| P4),
        r: Plated[(Q3 |*| Q4), Z2],
      ): Shuffled[A1 |*| A2, (Q1 |*| Q2) |*| Z2] =
        revDecompose1(f2) match {
          case RevDecomposition1(ev, lt, f21, f22) =>
            ~⚬.decompose(value.g2.asShuffle) match {
              case ~⚬.Decomposition(g21, g22, rt) =>
                Pure(~⚬.fst(f1) > ~⚬.assocLR) >
                  snd(Impermeable(~⚬.fst(g21), Plated.XI(ev.substituteCo(l), lt, f22 > g22, rt, r), ~⚬.fst(f21))) >
                  Pure(~⚬.assocRL > ~⚬.fst(value.g1.asShuffle))
            }
        }

    }

    def apply[P1, P2, Q1, Q2](t: Transfer[P1, P2, Q1, Q2]): Tr[P1, P2, Q1, Q2] =
      t match {
        case t: Transfer.Swap[_, _]                  => Swap(t)
        case t: Transfer.AssocLR[_, _, _, _, _]      => AssocLR(t)
        case t: Transfer.AssocRL[_, _, _, _, _]      => AssocRL(t)
        case t: Transfer.IX[_, _, _, _, _]           => IX(t)
        case t: Transfer.XI[_, _, _, _, _]           => XI(t)
        case t: Transfer.IXI[_, _, _, _, _, _, _, _] => IXI(t)
      }

    def revDecompose1[X, Z1, Z2](f: X ~⚬ (Z1 |*| Z2)): RevDecomposition1[X, _, _, _, _, Z1, Z2] =
      ~⚬.decompose1(f.invert) match {
        case ~⚬.Decomposition1(f1, f2, g, ev) =>
          RevDecomposition1(ev.flip, RevTransferOpt(g), f1.invert, f2.invert)
      }

    case class RevDecomposition1[X, X1, X2, Y1, Y2, Z1, Z2](
      ev: X =:= (X1 |*| X2),
      t: RevTransferOpt[X1, X2, Y1, Y2],
      g1: Y1 ~⚬ Z1,
      g2: Y2 ~⚬ Z2,
    )
  }

  enum UnconsSomeRes[A, B] {
    case Pure(s: A ~⚬ B)

    case Cons[A, F[_], X, Y, B](
      pre: A ~⚬ F[X],
      i: Focus[|*|, F],
      f: X -> Y,
      post: Shuffled[F[Y], B],
    ) extends UnconsSomeRes[A, B]
  }

  enum ChaseFwRes[F[_], X, B] {
    case Transported[F[_], X, G[_], B](s: [x] => Unit => Shuffled[F[x], G[x]], g: Focus[|*|, G], ev: G[X] =:= B) extends ChaseFwRes[F, X, B]

    case FedTo[F[_], X, V[_], W, G[_], B](
      pre: Shuffled[F[X], G[V[X]]],
      v: Focus[|*|, V],
      f: V[X] -> W,
      g: Focus[|*|, G],
      post: Shuffled[G[W], B],
    ) extends ChaseFwRes[F, X, B]

    case Split[F[_], X, X1, X2, B](ev: X =:= (X1 |*| X2)) extends ChaseFwRes[F, X, B]
  }

  enum ChaseBwRes[A, G[_], X] {
    case Transported[A, F[_], G[_], X](ev: A =:= F[X], f: Focus[|*|, F], s: [x] => Unit => Shuffled[F[x], G[x]]) extends ChaseBwRes[A, G, X]

    case OriginatesFrom[A, F[_], V, W[_], X, G[_]](
      pre: Shuffled[A, F[V]],
      i: Focus[|*|, F],
      f: V -> W[X],
      w: Focus[|*|, W],
      post: Shuffled[F[W[X]], G[X]],
    ) extends ChaseBwRes[A, G, X]

    case Split[A, G[_], X, X1, X2](ev: X =:= (X1 |*| X2)) extends ChaseBwRes[A, G, X]
  }

  enum ProjectRes[A, C] {
    case Projected[A0, A, C](p: Projection[|*|, A, A0], f: Shuffled[A0, C]) extends ProjectRes[A, C]
  }
}
