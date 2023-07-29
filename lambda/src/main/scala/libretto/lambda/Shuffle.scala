package libretto.lambda

import libretto.lambda.{Projection as P}
import libretto.lambda.util.{BiInjective, Exists, TypeEq}
import libretto.lambda.util.BiInjective.*
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.Projection.Proper

class Shuffle[|*|[_, _]](using inj: BiInjective[|*|]) {
  sealed trait ~⚬[A, B] {
    import ~⚬.*

    def >[C](that: B ~⚬ C): A ~⚬ C =
      (this, that) match {
        case (Id(), g) => g
        case (f, Id()) => f
        case (Bimap(Par(f1, f2)), Bimap(Par(g1, g2))) => par(f1 > g1, f2 > g2)
        case (Bimap(Par(f1, f2)), Xfer(g1, g2, h)) => Xfer(f1 > g1, f2 > g2, h)
        case (Xfer(f1, f2, g), Bimap(Par(h1, h2))) =>
          g.thenBi(h1, h2) match {
            case Xfer(g1, g2, h) => Xfer(f1 > g1, f2 > g2, h)
          }
        case (Xfer(f1, f2, g), Xfer(h1, h2, i)) =>
          g.thenBi(h1, h2) match {
            case Xfer(g1, g2, h) =>
              (h > i) match {
                case id: Id0[?, ?] => id.ev.substituteCo(par(f1 > g1, f2 > g2))
                case Bimap(Par(h1, h2)) => par(f1 > g1 > h1, f2 > g2 > h2)
                case Xfer(h1, h2, i) => Xfer(f1 > g1 > h1, f2 > g2 > h2, i)
              }
          }
      }

    def after[Z](that: Z ~⚬ A): Z ~⚬ B =
      that > this

    def invert: B ~⚬ A

    def fold[->[_, _]](using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B = {
      import ev.{andThen, id, par}

      this match {
        case Id()               => id
        case Bimap(Par(f1, f2)) => par(f1.fold, f2.fold)
        case Xfer(f1, f2, xfer) => andThen(par(f1.fold, f2.fold), xfer.fold)
      }
    }

    def projectProper[C](p: Projection.Proper[|*|, B, C]): ProjectProperRes[A, C]
    def chaseFw[F[_], X](i: Focus[|*|, F])(using ev: A =:= F[X]): ChaseFwRes[F, X, B]
    def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: B =:= G[X]): ChaseBwRes[A, G, X]

    def project[C](p: Projection[|*|, B, C]): ProjectRes[A, C] =
      p match {
        case Projection.Id()                 => ProjectRes.Projected(Projection.Id(), this)
        case p: Projection.Proper[|*|, B, C] => projectProper(p).unproper
      }

    def to[C](using ev: B =:= C): A ~⚬ C =
      ev.substituteCo(this)

    def from[Z](using ev: Z =:= A): Z ~⚬ B =
      ev.substituteContra[[a] =>> a ~⚬ B](this)

    def inFst[C, D](snd: C ~⚬ D): (A |*| C) ~⚬ (B |*| D) =
      par(this, snd)

    def inFst[C]: (A |*| C) ~⚬ (B |*| C) =
      fst(this)

    def inSnd[P, Q](fst: P ~⚬ Q): (P |*| A) ~⚬ (Q |*| B) =
      par(fst, this)

    def inSnd[P]: (P |*| A) ~⚬ (P |*| B) =
      snd(this)

    def at[F[_]](f: Focus[|*|, F]): F[A] ~⚬ F[B] =
      f match {
        case Focus.Id()    => this
        case Focus.Fst(f1) => fst(this.at(f1))
        case Focus.Snd(f2) => snd(this.at(f2))
      }

    /** Translate to a different product type. */
    def translate[<*>[_, _], F[_, _], X](
      fa: F[A, X],
    )(
      m: SemigroupalObjectMap[|*|, <*>, F],
      sh: Shuffle[<*>],
    ): Exists[[t] =>> (sh.~⚬[X, t], F[B, t])]

    def apply[F[_]](a: F[A])(using Cartesian[|*|, F]): F[B]
  }

  object ~⚬ {
    sealed trait Id0[A, B] extends (A ~⚬ B) {
      def ev: A =:= B
    }

    object Id0 {
      def apply[A, B](ev: A =:= B): Id0[A, B] =
        ev.substituteCo(Id[A]())
    }

    case class Id[X]() extends Id0[X, X] {
      override def invert: X ~⚬ X =
        this

      override def ev: X =:= X =
        summon[X =:= X]

      override def projectProper[C](p: Projection.Proper[|*|, X, C]): ProjectProperRes[X, C] =
        ProjectProperRes.Projected[C, X, C](p, id[C])

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: X =:= F[T]): ChaseFwRes[F, T, X] =
        ChaseFwRes.Transported[F, T, F, X]([t] => (_: Unit) => Id[F[t]](), i, ev.flip)

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: X =:= G[T]): ChaseBwRes[X, G, T] =
        ChaseBwRes.Transported[X, G, G, T](ev, i, [t] => (_: Unit) => Id[G[t]]())

      override def translate[<*>[_, _], F[_, _], S](
        fx: F[X, S],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
        sh: Shuffle[<*>],
      ): Exists[[t] =>> (sh.~⚬[S, t], F[X, t])] =
        Exists((sh.~⚬.id, fx))

      override def apply[F[_]](fx: F[X])(using Cartesian[|*|, F]): F[X] =
        fx
    }

    /** Non-[[Id]] combinators. */
    sealed trait Composed[X, Y] extends (X ~⚬ Y) {
      override def invert: Composed[Y, X] =
        this match {
          case Bimap(p) =>
            Bimap(p.invert)
          case Xfer(f1, f2, x) =>
            x.invert match {
              case Xfer(g1, g2, y) =>
                y.thenBi(f1.invert, f2.invert) match {
                  case Xfer(h1, h2, z) => Xfer(g1 > h1, g2 > h2, z)
                }
            }
        }
    }

    /** Two parallel operations, at least one of which is not [[Id]]. */
    case class Bimap[X1, X2, Y1, Y2](par: Par[X1, X2, Y1, Y2]) extends Composed[X1 |*| X2, Y1 |*| Y2] {
      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: (X1 |*| X2) =:= F[T]): ChaseFwRes[F, T, Y1 |*| Y2] =
        par.chaseFw(i)

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (Y1 |*| Y2) =:= G[T]): ChaseBwRes[X1 |*| X2, G, T] =
        par.chaseBw(i)

      override def projectProper[C](p: Projection.Proper[|*|, Y1 |*| Y2, C]): ProjectProperRes[X1 |*| X2, C] =
        par.projectProper(p)

      override def translate[<*>[_, _], F[_, _], S](
        fa: F[X1 |*| X2, S],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
        sh: Shuffle[<*>],
      ): Exists[[t] =>> (sh.~⚬[S, t], F[Y1 |*| Y2, t])] =
        par.translate(fa)(m, sh)

      override def apply[F[_]](a: F[X1 |*| X2])(using Cartesian[|*|, F]): F[Y1 |*| Y2] =
        par(a)
    }

    /** An operator that transfers resources across inputs. */
    case class Xfer[A1, A2, X1, X2, B1, B2](f1: A1 ~⚬ X1, f2: A2 ~⚬ X2, transfer: Transfer[X1, X2, B1, B2]) extends Composed[A1 |*| A2, B1 |*| B2] {
      override def projectProper[C](p: Projection.Proper[|*|, B1 |*| B2, C]): ProjectProperRes[A1 |*| A2, C] =
        transfer.projectProper(p) match {
          case ProjectProperRes.Projected(px, t) =>
            par(f1, f2).projectProper(px) match
              case ProjectProperRes.Projected(pa, f) =>
                ProjectProperRes.Projected(pa, f > t)
        }

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: (A1 |*| A2) =:= F[T]): ChaseFwRes[F, T, B1 |*| B2] = {
        val res0: ChaseFwRes[F, T, X1 |*| X2] =
          i match
            case Focus.Id() =>
              ChaseFwRes.Split(summon[T =:= F[T]] andThen ev.flip)
            case i: Focus.Fst[pair, f1, a2] =>
              (ev andThen summon[F[T] =:= (f1[T] |*| a2)]) match
                case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                  f1.chaseFw[f1, T](i.i).inFst(f2)
            case i: Focus.Snd[pair, f2, a1] =>
              (ev andThen summon[F[T] =:= (a1 |*| f2[T])]) match
                case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                  f2.chaseFw[f2, T](i.i).inSnd(f1)
        res0 match
          case ChaseFwRes.Split(ev) =>
            ChaseFwRes.Split(ev)
          case tr: ChaseFwRes.Transported[g, t, h, z] =>
            transfer.chaseFw[h, T](tr.g)(using tr.ev).after(tr.s)
      }

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[T]): ChaseBwRes[A1 |*| A2, G, T] =
        transfer.chaseBw(i) after par(f1, f2)

      override def apply[F[_]](a: F[A1 |*| A2])(using F: Cartesian[|*|, F]): F[B1 |*| B2] = {
        val (a1, a2) = F.unzip(a)
        val x1 = f1(a1)
        val x2 = f2(a2)
        transfer(F.zip(x1, x2))
      }

      override def translate[<*>[_,_], F[_,_], S](
        fa: F[A1 |*| A2, S],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
        sh: Shuffle[<*>],
      ): Exists[[t] =>> (sh.~⚬[S, t], F[B1 |*| B2, t])] = {
        m.unpair(fa)                                          match { case m.Unpaired.Impl(fa1, fa2) =>
        (f1.translate(fa1)(m, sh), f2.translate(fa2)(m, sh))  match { case (Exists.Some(x1), Exists.Some(x2)) =>
        transfer.translate(m.pair(x1._2, x2._2))(m, sh)       match { case Exists.Some(b) =>
        Exists((sh.~⚬.par(x1._1, x2._1) > b._1, b._2))
        }}}
      }
    }

    def id[X]: X ~⚬ X =
      Id()

    def swap[X, Y]: (X |*| Y) ~⚬ (Y |*| X) =
      Xfer(Id(), Id(), Transfer.Swap())

    def assocLR[X, Y, Z]: ((X |*| Y) |*| Z) ~⚬ (X |*| (Y |*| Z)) =
      Xfer(Id(), Id(), Transfer.AssocLR(TransferOpt.None()))

    def assocRL[X, Y, Z]: (X |*| (Y |*| Z)) ~⚬ ((X |*| Y) |*| Z) =
      Xfer(Id(), Id(), Transfer.AssocRL(TransferOpt.None()))

    def par[X1, X2, Y1, Y2](f1: X1 ~⚬ Y1, f2: X2 ~⚬ Y2): (X1 |*| X2) ~⚬ (Y1 |*| Y2) =
      (f1, f2) match {
        case (Id()                , Id()                ) => Id()
        case (Id()                , f2: Composed[X2, Y2]) => Bimap(Par.Snd(f2))
        case (f1: Composed[X1, Y1], Id()                ) => Bimap(Par.Fst(f1))
        case (f1: Composed[X1, Y1], f2: Composed[X2, Y2]) => Bimap(Par.Both(f1, f2))
      }

    def fst[X, Y, Z](f: X ~⚬ Y): (X |*| Z) ~⚬ (Y |*| Z) =
      f match {
        case Id() => Id()
        case f: Composed[X, Y] => Bimap(Par.Fst(f))
      }

    def snd[X, Y, Z](f: Y ~⚬ Z): (X |*| Y) ~⚬ (X |*| Z) =
      f match {
        case Id() => Id()
        case f: Composed[Y, Z] => Bimap(Par.Snd(f))
      }

    def xi[X, Y, Z]: (X |*| (Y |*| Z)) ~⚬ (Y |*| (X |*| Z)) =
      Xfer(Id(), Id(), Transfer.XI(TransferOpt.None()))

    def xi[A1, A2, A3, B2, B3](g: (A1 |*| A3) ~⚬ (B2 |*| B3)): (A1 |*| (A2 |*| A3)) ~⚬ (A2 |*| (B2 |*| B3)) =
      decompose(g) match {
        case Decomposition(g1, g2, h) => Xfer(g1, snd(g2), Transfer.XI(h))
      }

    def ix[X, Y, Z]: ((X |*| Y) |*| Z) ~⚬ ((X |*| Z) |*| Y) =
      Xfer(Id(), Id(), Transfer.IX(TransferOpt.None()))

    def ix[A1, A2, A3, B1, B2](g: (A1 |*| A3) ~⚬ (B1 |*| B2)): ((A1 |*| A2) |*| A3) ~⚬ ((B1 |*| B2) |*| A2) =
      decompose(g) match {
        case Decomposition(g1, g2, h) => Xfer(fst(g1), g2, Transfer.IX(h))
      }

    def ixi[W, X, Y, Z]: ((W |*| X) |*| (Y |*| Z)) ~⚬ ((W |*| Y) |*| (X |*| Z)) =
      Xfer(Id(), Id(), Transfer.IXI(TransferOpt.None(), TransferOpt.None()))

    def tryUntangle[X1, X2, Y1, Y2](
      f: (X1 |*| X2) ~⚬ (Y1 |*| Y2)
    ): Either[Xfer[X1, X2, ?, ?, Y1, Y2], (X1 ~⚬ Y1, X2 ~⚬ Y2)] =
      f match {
        case id: Id0[X1 |*| X2, Y1 |*| Y2] =>
          val inj(ev1, ev2) = id.ev
          val f1: X1 ~⚬ Y1 = ev1.substituteCo(Id[X1]())
          val f2: X2 ~⚬ Y2 = ev2.substituteCo(Id[X2]())
          Right((f1, f2))
        case Bimap(Par(f1, f2)) =>
          Right((f1, f2))
        case xfer @ Xfer(_, _, _) =>
          Left(xfer)
      }

    def decompose[X1, X2, Z1, Z2](f: (X1 |*| X2) ~⚬ (Z1 |*| Z2)): Decomposition[X1, X2, ?, ?, Z1, Z2] =
      f match {
        case i: Id0[X1 |*| X2, Z1 |*| Z2] => Decomposition(Id(), Id(), TransferOpt.None0(i.ev))
        case Bimap(Par(f1, f2))           => Decomposition(f1, f2, TransferOpt.None())
        case Xfer(f1, f2, xfer)           => Decomposition(f1, f2, xfer)
      }

    def decompose1[X1, X2, Z](f: (X1 |*| X2) ~⚬ Z): Decomposition1[X1, X2, ?, ?, ?, ?, Z] =
      f match {
        case Id()               => Decomposition1(Id(), Id(), TransferOpt.None(), summon)
        case Bimap(Par(f1, f2)) => Decomposition1(f1, f2, TransferOpt.None(), implicitly)
        case Xfer(f1, f2, xfer) => Decomposition1(f1, f2, xfer, implicitly)
      }

    case class Decomposition[X1, X2, Y1, Y2, Z1, Z2](
      f1: X1 ~⚬ Y1,
      f2: X2 ~⚬ Y2,
      g: TransferOpt[Y1, Y2, Z1, Z2],
    )

    case class Decomposition1[X1, X2, Y1, Y2, Z1, Z2, Z](
      f1: X1 ~⚬ Y1,
      f2: X2 ~⚬ Y2,
      g: TransferOpt[Y1, Y2, Z1, Z2],
      ev: (Z1 |*| Z2) =:= Z,
    )

    sealed trait ChaseFwRes[F[_], X, B] {
      def andThen[C](g: B ~⚬ C): ChaseFwRes[F, X, C]
      def after[F0[_]](f: [x] => Unit => F0[x] ~⚬ F[x]): ChaseFwRes[F0, X, B]
      def inFst[C, D](snd: C ~⚬ D): ChaseFwRes[[x] =>> F[x] |*| C, X, B |*| D]
      def inSnd[Y, Z](fst: Y ~⚬ Z): ChaseFwRes[[x] =>> Y |*| F[x], X, Z |*| B]

      def inFst[C]: ChaseFwRes[[x] =>> F[x] |*| C, X, B |*| C] = inFst(id[C])
      def inSnd[Z]: ChaseFwRes[[x] =>> Z |*| F[x], X, Z |*| B] = inSnd(id[Z])

      def thenSnd[B1, B2, C](f: B2 ~⚬ C)(using B =:= (B1 |*| B2)): ChaseFwRes[F, X, B1 |*| C]
    }

    object ChaseFwRes {
      case class Transported[F[_], X, G[_], B](
        s: [t] => Unit => F[t] ~⚬ G[t],
        g: Focus[|*|, G],
        ev: G[X] =:= B,
      ) extends ChaseFwRes[F, X, B] {
        override def inFst[C, D](snd: C ~⚬ D): ChaseFwRes[[x] =>> F[x] |*| C, X, B |*| D] =
          Transported[[x] =>> F[x] |*| C, X, [x] =>> G[x] |*| D, B |*| D](
            [t] => (_: Unit) => par(s[t](()), snd),
            g.inFst,
            ev zip summon,
          )

        override def inSnd[Y, Z](fst: Y ~⚬ Z): ChaseFwRes[[x] =>> Y |*| F[x], X, Z |*| B] =
          Transported[[x] =>> Y |*| F[x], X, [x] =>> Z |*| G[x], Z |*| B](
            [t] => (_: Unit) => par(fst, s[t](())),
            g.inSnd,
            summon[Z =:= Z] zip ev,
          )

        override def andThen[C](h: B ~⚬ C): ChaseFwRes[F, X, C] =
          h.chaseFw[G, X](g)(using ev.flip) match
            case t: Transported[g, x, h, c] => Transported[F, X, h, C]([t] => (_: Unit) => s[t](()) > t.s[t](()), t.g, t.ev)
            case Split(ev) => Split(ev)

        override def after[F0[_]](f: [x] => Unit => F0[x] ~⚬ F[x]): ChaseFwRes[F0, X, B] =
          Transported[F0, X, G, B]([t] => (_: Unit) => f[t](()) > s[t](()), g, ev)

        override def thenSnd[B1, B2, C](f: B2 ~⚬ C)(using ev1: B =:= (B1 |*| B2)): ChaseFwRes[F, X, B1 |*| C] =
          g match {
            case Focus.Id() =>
              Split(ev andThen ev1)
            case g: Focus.Fst[pair, g1, z] =>
              (summon[(g1[X] |*| z) =:= G[X]] andThen ev andThen ev1)                 match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[F, X, [x] =>> g1[x] |*| C, B1 |*| C](
                  [t] => (_: Unit) => s[t](()) > snd(f),
                  g.i.inFst[C],
                  summon,
                )
              }
            case g: Focus.Snd[pair, g2, z] =>
              (summon[(z |*| g2[X]) =:= G[X]] andThen ev andThen ev1)                 match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                f.chaseFw[g2, X](g.i).inSnd[B1].after(s)
              }
          }
      }

      case class Split[F[_], X, X1, X2, B](ev: X =:= (X1 |*| X2)) extends ChaseFwRes[F, X, B] {
        override def inFst[C, D](snd: C ~⚬ D): ChaseFwRes[[x] =>> F[x] |*| C, X, B |*| D] = Split(ev)
        override def inSnd[Y, Z](fst: Y ~⚬ Z): ChaseFwRes[[x] =>> Y |*| F[x], X, Z |*| B] = Split(ev)
        override def andThen[C](g: B ~⚬ C): ChaseFwRes[F, X, C] = Split(ev)
        override def after[F0[_]](f: [x] => Unit => F0[x] ~⚬ F[x]): ChaseFwRes[F0, X, B] = Split(ev)
        override def thenSnd[B1, B2, C](f: B2 ~⚬ C)(using B =:= (B1 |*| B2)): ChaseFwRes[F, X, B1 |*| C] = Split(ev)
      }
    }

    sealed trait ChaseBwRes[A, G[_], X] {
      def after[Z](f: Z ~⚬ A): ChaseBwRes[Z, G, X]
      def andThen[H[_]](h: [x] => Unit => G[x] ~⚬ H[x]): ChaseBwRes[A, H, X]
      def inFst[B, C](snd: B ~⚬ C): ChaseBwRes[A |*| B, [x] =>> G[x] |*| C, X]
      def inSnd[Y, Z](fst: Y ~⚬ Z): ChaseBwRes[Y |*| A, [x] =>> Z |*| G[x], X]

      def inFst[B]: ChaseBwRes[A |*| B, [x] =>> G[x] |*| B, X] = inFst(id[B])
      def inSnd[Z]: ChaseBwRes[Z |*| A, [x] =>> Z |*| G[x], X] = inSnd(id[Z])

      def afterAssocLR[A1, A2, A3](using (A2 |*| A3) =:= A): ChaseBwRes[(A1 |*| A2) |*| A3, [x] =>> A1 |*| G[x], X]
      def afterAssocRL[A1, A2, A3](using (A1 |*| A2) =:= A): ChaseBwRes[A1 |*| (A2 |*| A3), [x] =>> G[x] |*| A3, X]
      def afterXI[A1, A2, A3](using (A1 |*| A3) =:= A): ChaseBwRes[A1 |*| (A2 |*| A3), [x] =>> A2 |*| G[x], X]
      def afterIX[A1, A2, A3](using (A1 |*| A3) =:= A): ChaseBwRes[(A1 |*| A2) |*| A3, [x] =>> G[x] |*| A2, X]
      def afterIXI1[A1, A2, A3, A4](using (A1 |*| A3) =:= A): ChaseBwRes[(A1 |*| A2) |*| (A3 |*| A4), [x] =>> G[x] |*| (A2 |*| A4), X]
    }

    object ChaseBwRes {
      case class Transported[A, F[_], G[_], X](
        ev: A =:= F[X],
        f: Focus[|*|, F],
        s: [t] => Unit => F[t] ~⚬ G[t],
      ) extends ChaseBwRes[A, G, X] {
        override def after[Z](g: Z ~⚬ A): ChaseBwRes[Z, G, X] =
          g.chaseBw(f)(using ev) match
            case Transported(ev0, f0, s0) => Transported(ev0, f0, [t] => (_: Unit) => s0[t](()) > s[t](()))
            case Split(ev) => Split(ev)

        override def andThen[H[_]](h: [x] => Unit => G[x] ~⚬ H[x]): ChaseBwRes[A, H, X] =
          Transported(ev, f, [x] => (_: Unit) => s[x](()) > h[x](()))

        override def inFst[B, C](snd: B ~⚬ C): ChaseBwRes[A |*| B, [x] =>> G[x] |*| C, X] =
          Transported[A |*| B, [x] =>> F[x] |*| B, [x] =>> G[x] |*| C, X](
            ev zip summon,
            f.inFst,
            [t] => (_: Unit) => par(s[t](()), snd),
          )

        override def inSnd[Y, Z](fst: Y ~⚬ Z): ChaseBwRes[Y |*| A, [x] =>> Z |*| G[x], X] =
          Transported[Y |*| A, [x] =>> Y |*| F[x], [x] =>> Z |*| G[x], X](
            summon[Y =:= Y] zip ev,
            f.inSnd,
            [t] => (_: Unit) => par(fst, s[t](())),
          )

        override def afterAssocLR[A1, A2, A3](using ev1: (A2 |*| A3) =:= A): ChaseBwRes[(A1 |*| A2) |*| A3, [x] =>> A1 |*| G[x], X] =
          f match {
            case Focus.Id() =>
              Split(ev.flip andThen ev1.flip)
            case f: Focus.Fst[pair, f1, z] =>
              (ev1 andThen ev andThen summon[F[X] =:= (f1[X] |*| z)])                                   match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[(A1 |*| A2) |*| A3, [x] =>> (A1 |*| f1[x]) |*| A3, [x] =>> A1 |*| G[x], X](
                  summon,
                  f.i.inSnd[A1].inFst[A3],
                  [x] => (_: Unit) => assocLR > snd(s[x](())),
                )
              }
            case f: Focus.Snd[pair, f2, z] =>
              (ev1 andThen ev andThen summon[F[X] =:= (z |*| f2[X])])                                   match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[(A1 |*| A2) |*| A3, [x] =>> (A1 |*| A2) |*| f2[x], [x] =>> A1 |*| G[x], X](
                  summon,
                  f.i.inSnd[A1 |*| A2],
                  [x] => (_: Unit) => assocLR > snd(s[x](())),
                )
              }
          }

        override def afterAssocRL[A1, A2, A3](using ev1: (A1 |*| A2) =:= A): ChaseBwRes[A1 |*| (A2 |*| A3), [x] =>> G[x] |*| A3, X] =
          f match {
            case Focus.Id() =>
              Split(ev.flip andThen ev1.flip)
            case f: Focus.Fst[pair, f1, a2] =>
              (ev1 andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[A1 |*| (A2 |*| A3), [t] =>> f1[t] |*| (A2 |*| A3), [t] =>> G[t] |*| A3, X](
                  summon,
                  f.i.inFst[A2 |*| A3],
                  [t] => (_: Unit) => assocRL[f1[t], A2, A3] > fst(s[t](())),
                )
              }
            case f: Focus.Snd[pair, f2, a1] =>
              (ev1 andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[A1 |*| (A2 |*| A3), [t] =>> A1 |*| (f2[t] |*| A3), [t] =>> G[t] |*| A3, X](
                  summon,
                  f.i.inFst[A3].inSnd[A1],
                  [t] => (_: Unit) => assocRL[A1, f2[t], A3] > fst(s[t](())),
                )
              }
          }

        override def afterXI[A1, A2, A3](using ev1: (A1 |*| A3) =:= A): ChaseBwRes[A1 |*| (A2 |*| A3), [x] =>> A2 |*| G[x], X] =
          f match {
            case Focus.Id() =>
              Split(ev.flip andThen ev1.flip)
            case j: Focus.Fst[pair, f1, q] =>
              (ev1 andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[A1 |*| (A2 |*| A3), [t] =>> f1[t] |*| (A2 |*| A3), [x] =>> A2 |*| G[x], X](
                  summon,
                  j.i.inFst[A2 |*| A3],
                  [t] => (_: Unit) => xi[f1[t], A2, A3] > snd(s[t](())),
                )
              }
            case j: Focus.Snd[pair, f2, p] =>
              (ev1 andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[A1 |*| (A2 |*| A3), [t] =>> A1 |*| (A2 |*| f2[t]), [x] =>> A2 |*| G[x], X](
                  summon,
                  j.i.inSnd[A2].inSnd[A1],
                  [t] => (_: Unit) => xi[A1, A2, f2[t]] > snd(s[t](())),
                )
              }
            }

        override def afterIX[A1, A2, A3](using ev1: (A1 |*| A3) =:= A): ChaseBwRes[(A1 |*| A2) |*| A3, [x] =>> G[x] |*| A2, X] =
          f match {
            case Focus.Id() =>
              Split(ev.flip andThen ev1.flip)
            case f: Focus.Fst[pair, f1, a3] =>
              (ev1 andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[(A1 |*| A2) |*| A3, [t] =>> (f1[t] |*| A2) |*| A3, [x] =>> G[x] |*| A2, X](
                  summon,
                  f.i.inFst[A2].inFst[A3],
                  [x] => (_: Unit) => ix > fst(s[x](())),
                )
              }
            case f: Focus.Snd[pair, f2, a1] =>
              (ev1 andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[(A1 |*| A2) |*| A3, [t] =>> (A1 |*| A2) |*| f2[t], [x] =>> G[x] |*| A2, X](
                  summon,
                  f.i.inSnd[A1 |*| A2],
                  [x] => (_: Unit) => ix > fst(s[x](())),
                )
              }
          }

        override def afterIXI1[A1, A2, A3, A4](using ev1: (A1 |*| A3) =:= A): ChaseBwRes[(A1 |*| A2) |*| (A3 |*| A4), [x] =>> G[x] |*| (A2 |*| A4), X] =
          f match {
            case Focus.Id() =>
              Split(ev.flip andThen ev1.flip)
            case f: Focus.Fst[pair, f1, a3] =>
              (ev1 andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[(A1 |*| A2) |*| (A3 |*| A4), [x] =>> (f1[x] |*| A2) |*| (A3 |*| A4), [x] =>> G[x] |*| (A2 |*| A4), X](
                  summon,
                  f.i.inFst[A2].inFst[A3 |*| A4],
                  [x] => (_: Unit) => ixi > fst(s[x](())),
                )
              }
            case f: Focus.Snd[pair, f2, a1] =>
              (ev1 andThen ev) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                Transported[(A1 |*| A2) |*| (A3 |*| A4), [x] =>> (A1 |*| A2) |*| (f2[x] |*| A4), [x] =>> G[x] |*| (A2 |*| A4), X](
                  summon,
                  f.i.inFst[A4].inSnd[A1 |*| A2],
                  [x] => (_: Unit) => ixi > fst(s[x](())),
                )
              }
          }

        // def fromPair[A1, A2](using A =:= (A1 |*| A2)): FromPair[A1, A2] =
        //   new FromPair

        // class FromPair[A1, A2](using ev1: A =:= (A1 |*| A2)) {
        //   def switch[R](
        //     caseId: (A =:= X) ?=> ([t] => Unit => t ~⚬ G[t]) => R,
        //     caseFst: [F1[_]] => (A1 =:= F1[X]) ?=> (Focus[|*|, F1], [t] => Unit => (F1[t] |*| A2) ~⚬ G[t]) => R,
        //     caseSnd: [F2[_]] => (A2 =:= F2[X]) ?=> (Focus[|*|, F2], [t] => Unit => (A1 |*| F2[t]) ~⚬ G[t]) => R,
        //   ): R =
        //     f match {
        //       case Focus.Id() =>
        //         caseId(using ev)(s)
        //       case f: Focus.Fst[pair, f1, a2] =>
        //         (ev1.flip andThen ev andThen summon[F[X] =:= (f1[X] |*| a2)]) match
        //           case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
        //             caseFst[f1](f.i, s)
        //       case f: Focus.Snd[pair, f2, a1] =>
        //         (ev1.flip andThen ev andThen summon[F[X] =:= (a1 |*| f2[X])]) match
        //           case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
        //             caseSnd[f2](f.i, s)
        //     }
        // }
      }

      case class Split[A, G[_], X, X1, X2](ev: X =:= (X1 |*| X2)) extends ChaseBwRes[A, G, X] {
        override def after[Z](f: Z ~⚬ A): ChaseBwRes[Z, G, X] = Split(ev)
        override def andThen[H[_]](h: [x] => Unit => G[x] ~⚬ H[x]): ChaseBwRes[A, H, X] = Split(ev)
        override def inFst[B, C](snd: B ~⚬ C): ChaseBwRes[A |*| B, [x] =>> G[x] |*| C, X] = Split(ev)
        override def inSnd[Y, Z](fst: Y ~⚬ Z): ChaseBwRes[Y |*| A, [x] =>> Z |*| G[x], X] = Split(ev)
        override def afterAssocLR[A1, A2, A3](using (A2 |*| A3) =:= A): ChaseBwRes[(A1 |*| A2) |*| A3, [x] =>> A1 |*| G[x], X] = Split(ev)
        override def afterAssocRL[A1, A2, A3](using (A1 |*| A2) =:= A): ChaseBwRes[A1 |*| (A2 |*| A3), [x] =>> G[x] |*| A3, X] = Split(ev)
        override def afterXI[A1, A2, A3](using (A1 |*| A3) =:= A): ChaseBwRes[A1 |*| (A2 |*| A3), [x] =>> A2 |*| G[x], X] = Split(ev)
        override def afterIX[A1, A2, A3](using (A1 |*| A3) =:= A): ChaseBwRes[(A1 |*| A2) |*| A3, [x] =>> G[x] |*| A2, X] = Split(ev)
        override def afterIXI1[A1, A2, A3, A4](using (A1 |*| A3) =:= A): ChaseBwRes[(A1 |*| A2) |*| (A3 |*| A4), [x] =>> G[x] |*| (A2 |*| A4), X] = Split(ev)
      }
    }

    enum ProjectRes[A, C] {
      case Projected[A0, A, C](p: Projection[|*|, A, A0], f: A0 ~⚬ C) extends ProjectRes[A, C]
    }

    sealed trait ProjectProperRes[A, C] {
      type X
      val p: Projection.Proper[|*|, A, X]
      val f: X ~⚬ C

      import ProjectProperRes.*

      def unproper: ProjectRes[A, C] =
        this match
          case Projected(p, f) => ProjectRes.Projected(p, f)

      def project[D](p2: Projection[|*|, C, D]): ProjectProperRes[A, D] =
        this match
          case Projected(p0, f) =>
            f.project(p2) match
              case ProjectRes.Projected(p1, f1) => Projected(p0 > p1, f1)

      def to[D](using ev: C =:= D): ProjectProperRes[A, D] =
        ev.substituteCo(this)
    }

    object ProjectProperRes {
      case class Projected[A0, A, C](p: Projection.Proper[|*|, A, A0], f: A0 ~⚬ C) extends ProjectProperRes[A, C] {
        override type X = A0
      }
    }
  }
  import ~⚬.*

  /** Two parallel operations, at least one of which is not [[Id]]. */
  enum Par[X1, X2, Y1, Y2] {
    case Fst[X, Y, Z](f1: Composed[X, Y]) extends Par[X, Z, Y, Z]
    case Snd[X, Y, Z](f2: Composed[Y, Z]) extends Par[X, Y, X, Z]
    case Both[X1, X2, Y1, Y2](f1: Composed[X1, Y1], f2: Composed[X2, Y2]) extends Par[X1, X2, Y1, Y2]

    def invert: Par[Y1, Y2, X1, X2] =
      this match {
        case Fst(f1)      => Fst(f1.invert)
        case Snd(f2)      => Snd(f2.invert)
        case Both(f1, f2) => Both(f1.invert, f2.invert)
      }

    def projectProper[C](p: Projection.Proper[|*|, Y1 |*| Y2, C]): ProjectProperRes[X1 |*| X2, C] = {
      import libretto.lambda.{Projection as P}
      val Par(f1, f2) = this
      p.fromPair[Y1, Y2].switch[ProjectProperRes[X1 |*| X2, C]](
        caseDiscardFst = { p2 =>
          f2.project(p2) match
            case ProjectRes.Projected(p0, f0) => ProjectProperRes.Projected(P.discardFst(p0), f0)
        },
        caseDiscardSnd = { p1 =>
          f1.project(p1) match
            case ProjectRes.Projected(p0, f0) => ProjectProperRes.Projected(P.discardSnd(p0), f0)
        },
        casePar = [q1, q2] => (ev: C =:= (q1 |*| q2)) ?=> (p: P.Par[|*|, Y1, Y2, q1, q2]) =>                                                      ev match { case TypeEq(Refl()) =>
          p match
            case P.Fst(p1) =>
              f1.projectProper(p1) match
                case ProjectProperRes.Projected(p0, f0) => ProjectProperRes.Projected(P.Fst(p0), par(f0, f2).to[C])
            case P.Snd(p2) =>
              f2.projectProper(p2) match
                case ProjectProperRes.Projected(p0, f0) => ProjectProperRes.Projected(P.Snd(p0), par(f1, f0).to[C])
            case P.Both(p1, p2) =>
              (f1.projectProper(p1), f2.projectProper(p2)) match
                case (ProjectProperRes.Projected(q1, g1), ProjectProperRes.Projected(q2, g2)) =>
                  ProjectProperRes.Projected(P.Both(q1, q2), par(g1, g2).to[C])
        },
      )
    }

    def apply[F[_]](fx: F[X1 |*| X2])(using F: Cartesian[|*|, F]): F[Y1 |*| Y2] = {
      val (f1, f2) = Par.unapply(this)
      val (x1, x2) = F.unzip(fx)
      F.zip(f1(x1), f2(x2))
    }

    def translate[<*>[_, _], F[_, _], S](
      fa: F[X1 |*| X2, S],
    )(
      m: SemigroupalObjectMap[|*|, <*>, F],
      sh: Shuffle[<*>],
    ): Exists[[t] =>> (sh.~⚬[S, t], F[Y1 |*| Y2, t])] = {
      this                        match { case Par(f1, f2) =>
      m.unpair(fa)                match { case m.Unpaired.Impl(fx1, fx2) =>
      f1.translate(fx1)(m, sh)    match { case Exists.Some(y1) =>
      f2.translate(fx2)(m, sh)    match { case Exists.Some(y2) =>
      Exists((
        sh.~⚬.par(y1._1, y2._1),
        m.pair(y1._2, y2._2),
      ))
      }}}}
    }

    def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: (X1 |*| X2) =:= F[T]): ChaseFwRes[F, T, Y1 |*| Y2] =
      i match {
        case Focus.Id() =>
          ChaseFwRes.Split(ev.flip)
        case i: Focus.Fst[pair, f1, x2] =>
          (ev andThen summon[F[T] =:= (f1[T] |*| x2)]) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            this match
              case Snd(f2) =>
                ChaseFwRes.Transported[F, T, [t] =>> f1[t] |*| Y2, Y1 |*| Y2](
                  [t] => (_: Unit) => par(id, f2),
                  i.i.inFst,
                  summon,
                )
              case Fst(f1) =>
                f1.chaseFw[f1, T](i.i).inFst[Y2]
              case Both(f1, f2) =>
                f1.chaseFw[f1, T](i.i).inFst(f2)
          }
        case i: Focus.Snd[pair, f2, x1] =>
          (ev andThen summon[F[T] =:= (x1 |*| f2[T])]) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            this match
              case Fst(f1) =>
                ChaseFwRes.Transported[F, T, [t] =>> Y1 |*| f2[t], Y1 |*| Y2](
                  [t] => (_: Unit) => par(f1, id),
                  i.i.inSnd,
                  summon,
                )
              case Snd(f2) =>
                f2.chaseFw[f2, T](i.i).inSnd[Y1]
              case Both(f1, f2) =>
                f2.chaseFw[f2, T](i.i).inSnd(f1)
          }
      }

    def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (Y1 |*| Y2) =:= G[T]): ChaseBwRes[X1 |*| X2, G, T] =
      i match {
        case Focus.Id() =>
          ChaseBwRes.Split(ev.flip)
        case i: Focus.Fst[pair, g1, y2] =>
          (ev andThen summon[G[T] =:= (g1[T] |*| y2)]) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            this match
              case Snd(f2) =>
                ChaseBwRes.Transported[X1 |*| X2, [t] =>> g1[t] |*| X2, G, T](
                  summon,
                  i.i.inFst,
                  [t] => (_: Unit) => par(id, f2),
                )
              case Fst(f1) =>
                f1.chaseBw[g1, T](i.i).inFst[X2]
              case Both(f1, f2) =>
                f1.chaseBw[g1, T](i.i).inFst(f2)
          }
        case i: Focus.Snd[pair, g2, y1] =>
          (ev andThen summon[G[T] =:= (y1 |*| g2[T])]) match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            this match
              case Fst(f1) =>
                ChaseBwRes.Transported[X1 |*| X2, [t] =>> X1 |*| g2[t], G, T](
                  summon,
                  i.i.inSnd,
                  [t] => (_: Unit) => par(f1, id),
                )
              case Snd(f2) =>
                f2.chaseBw[g2, T](i.i).inSnd[X1]
              case Both(f1, f2) =>
                f2.chaseBw[g2, T](i.i).inSnd(f1)
          }
      }
  }

  object Par {
    def unapply[X1, X2, Y1, Y2](p: Par[X1, X2, Y1, Y2]): (X1 ~⚬ Y1, X2 ~⚬ Y2) =
      p match {
        case Fst(f1) => (f1, Id())
        case Snd(f2) => (Id(), f2)
        case Both(f1, f2) => (f1, f2)
      }
  }

  sealed trait TransferOpt[A1, A2, B1, B2] {
    def fold[->[_, _]](using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> (B1 |*| B2)

    def apply[F[_]](a: F[A1 |*| A2])(using F: Cartesian[|*|, F]): F[B1 |*| B2]
    def projectProper[C](p: Projection.Proper[|*|, B1 |*| B2, C]): ProjectProperRes[A1 |*| A2, C]
    def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A1 |*| A2)): ChaseFwRes[F, T, B1 |*| B2]
    def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[T]): ChaseBwRes[A1 |*| A2, G, T]
    def chaseFwFst[F[_], T](i: Focus[|*|, F])(using F[T] =:= A1): ChaseFwRes[[t] =>> F[t] |*| A2, T, B1 |*| B2]
    def chaseFwSnd[F[_], T](i: Focus[|*|, F])(using F[T] =:= A2): ChaseFwRes[[t] =>> A1 |*| F[t], T, B1 |*| B2]
    def chaseBwFst[G[_], T](i: Focus[|*|, G])(using B1 =:= G[T]): ChaseBwRes[A1 |*| A2, [t] =>> G[t] |*| B2, T]
    def chaseBwSnd[G[_], T](i: Focus[|*|, G])(using B2 =:= G[T]): ChaseBwRes[A1 |*| A2, [t] =>> B1 |*| G[t], T]

    final def translate[<*>[_, _], F[_, _], S](
      fa: F[A1 |*| A2, S],
    )(
      m: SemigroupalObjectMap[|*|, <*>, F],
      tgt: Shuffle[<*>],
    ): Exists[[t] =>> (tgt.~⚬[S, t], F[B1 |*| B2, t])] =
      m.unpair(fa) match
        case m.Unpaired.Impl(fa1, fa2) =>
          translateLR(fa1, fa2)(m)(using tgt) match
            case Exists.Some(Exists.Some((t, f1, f2))) =>
              Exists((t.asShuffle, m.pair(f1, f2)))

    def translateLR[<*>[_, _], F[_, _], S1, S2](
      fa1: F[A1, S1],
      fa2: F[A2, S2],
    )(
      m: SemigroupalObjectMap[|*|, <*>, F],
    )(using
      tgt: Shuffle[<*>],
    ): Exists[[T1] =>> Exists[[T2] =>> (tgt.TransferOpt[S1, S2, T1, T2], F[B1, T1], F[B2, T2])]]

    def translateRL[<*>[_, _], F[_, _], T1, T2](
      fb1: F[B1, T1],
      fb2: F[B2, T2],
    )(
      m: SemigroupalObjectMap[|*|, <*>, F],
    )(using
      tgt: Shuffle[<*>],
    ): Exists[[S1] =>> Exists[[S2] =>> (F[A1, S1], F[A2, S2], tgt.TransferOpt[S1, S2, T1, T2])]]

    def project[C](p: Projection[|*|, B1 |*| B2, C]): ProjectRes[A1 |*| A2, C] =
      p match {
        case Projection.Id()                    => ProjectRes.Projected(Projection.id, this.asShuffle)
        case p: Projection.Proper[|*|, b1b2, c] => projectProper(p).unproper
      }

    def pairWith[X3, X4, Z1, Z2](
      that: TransferOpt[X3, X4, Z1, Z2],
    ): BiTransferOpt[A1, A2, X3, X4, B1, B2, Z1, Z2]

    def nonePairWith_:[X1, X2](
      that: TransferOpt.None[X1, X2],
    ): BiTransferOpt[X1, X2, A1, A2, X1, X2, B1, B2]

    def swapPairWith_:[X1, X2](
      that: Transfer.Swap[X1, X2],
    ): BiTransferOpt[X1, X2, A1, A2, X2, X1, B1, B2]

    def ixiPairWith_:[X1, X2, X3, X4, Y1, Y2, Y3, Y4](
      that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2, Y3, Y4],
    ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1, A2, Y1 |*| Y2, Y3 |*| Y4, B1, B2]

    def asShuffle: (A1 |*| A2) ~⚬ (B1 |*| B2) =
      this match {
        case x: Transfer[?, ?, ?, ?] => Xfer(Id(), Id(), x)
        case TransferOpt.None() => Id()
      }
  }

  object TransferOpt {
    sealed trait None0[A1, A2, B1, B2] extends TransferOpt[A1, A2, B1, B2] {
      def ev1: A1 =:= B1
      def ev2: A2 =:= B2
    }

    object None0 {
      def apply[A1, A2, B1, B2](ev: (A1 |*| A2) =:= (B1 |*| B2)): None0[A1, A2, B1, B2] =
        ev.biSubst(None[A1, A2]())
    }

    case class None[A1, A2]() extends None0[A1, A2, A1, A2] {
      override def fold[->[_, _]](using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> (A1 |*| A2) =
        ev.id

      override def ev1: A1 =:= A1 =
        summon[A1 =:= A1]

      override def ev2: A2 =:= A2 =
        summon[A2 =:= A2]

      override def pairWith[X3, X4, Y3, Y4](
        that: TransferOpt[X3, X4, Y3, Y4],
      ): BiTransferOpt[A1, A2, X3, X4, A1, A2, Y3, Y4] =
       this nonePairWith_: that

      override def nonePairWith_:[X1, X2](
        that: TransferOpt.None[X1, X2],
      ): BiTransferOpt[X1, X2, A1, A2, X1, X2, A1, A2] =
        BiTransferOpt.None_None[X1, X2, A1, A2]()

      override def swapPairWith_:[X1, X2](
        that: Transfer.Swap[X1, X2],
      ): BiTransferOpt[X1, X2, A1, A2, X2, X1, A1, A2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def ixiPairWith_:[X1, X2, X3, X4, Y1, Y2, Y3, Y4](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2, Y3, Y4],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1, A2, Y1 |*| Y2, Y3 |*| Y4, A1, A2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")

      override def projectProper[C](p: Projection.Proper[|*|, A1 |*| A2, C]): ProjectProperRes[A1 |*| A2, C] =
        ProjectProperRes.Projected(p, id[C])

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A1 |*| A2)): ChaseFwRes[F, T, A1 |*| A2] =
        ChaseFwRes.Transported[F, T, F, A1 |*| A2]([t] => (_: Unit) => id[F[t]], i, ev)

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (A1 |*| A2) =:= G[T]): ChaseBwRes[A1 |*| A2, G, T] =
        ChaseBwRes.Transported[A1 |*| A2, G, G, T](ev, i, [t] => (_: Unit) => id[G[t]])

      override def chaseFwFst[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= A1): ChaseFwRes[[t] =>> F[t] |*| A2, T, A1 |*| A2] =
        ev match { case TypeEq(Refl()) => chaseFw(i.inFst[A2]) }

      override def chaseFwSnd[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= A2): ChaseFwRes[[t] =>> A1 |*| F[t], T, A1 |*| A2] =
        ev match { case TypeEq(Refl()) => chaseFw(i.inSnd[A1]) }

      override def chaseBwFst[G[_], T](i: Focus[|*|, G])(using ev: A1 =:= G[T]): ChaseBwRes[A1 |*| A2, [t] =>> G[t] |*| A2, T] =
        ev match { case TypeEq(Refl()) => chaseBw(i.inFst[A2]) }

      override def chaseBwSnd[G[_], T](i: Focus[|*|, G])(using ev: A2 =:= G[T]): ChaseBwRes[A1 |*| A2, [t] =>> A1 |*| G[t], T] =
        ev match { case TypeEq(Refl()) => chaseBw(i.inSnd[A1]) }

      override def apply[F[_]](a: F[A1 |*| A2])(using F: Cartesian[|*|, F]): F[A1 |*| A2] =
        a

      override def translateLR[<*>[_, _], F[_, _], S1, S2](
        fa1: F[A1, S1],
        fa2: F[A2, S2],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[T1] =>> Exists[[T2] =>> (tgt.TransferOpt[S1, S2, T1, T2], F[A1, T1], F[A2, T2])]] =
        Exists(Exists(tgt.TransferOpt.None(), fa1, fa2))

      override def translateRL[<*>[_, _], F[_, _], T1, T2](
        fb1: F[A1, T1],
        fb2: F[A2, T2],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[S1] =>> Exists[[S2] =>> (F[A1, S1], F[A2, S2], tgt.TransferOpt[S1, S2, T1, T2])]] =
        Exists(Exists((fb1, fb2, tgt.TransferOpt.None())))
    }

    def decompose[A1, A2, B1, B2](f: TransferOpt[A1, A2, B1, B2]): Either[Transfer[A1, A2, B1, B2], (Id0[A1, B1], Id0[A2, B2])] =
      f match {
        case t: Transfer[A1, A2, B1, B2] =>
          Left(t)
        case n: TransferOpt.None0[A1, A2, B1, B2] =>
          Right((Id0(n.ev1)), Id0(n.ev2))
      }
  }

  sealed trait Transfer[A1, A2, B1, B2] extends TransferOpt[A1, A2, B1, B2] {
    import Transfer.*

    def after[Z1, Z2](that: Transfer[Z1, Z2, A1, A2]): (Z1 |*| Z2) ~⚬ (B1 |*| B2)

    def thenBi[C1, C2](g1: B1 ~⚬ C1, g2: B2 ~⚬ C2): Xfer[A1, A2, ?, ?, C1, C2]

    def thenSwap: (A1 |*| A2) ~⚬ (B2 |*| B1)

    def thenAssocLR[B11, B12, C2, C3](
      that: AssocLR[B11, B12, B2, C2, C3],
    )(using
      ev: B1 =:= (B11 |*| B12),
    ): (A1 |*| A2) ~⚬ (B11 |*| (C2 |*| C3))

    def thenAssocRL[B21, B22, C1, C2](
      that: AssocRL[B1, B21, B22, C1, C2],
    )(using
      ev: B2 =:= (B21 |*| B22),
    ): (A1 |*| A2) ~⚬ ((C1 |*| C2) |*| B22)

    def thenIX[B11, B12, C1, C2](
      that: IX[B11, B12, B2, C1, C2],
    )(using
      ev: B1 =:= (B11 |*| B12),
    ): (A1 |*| A2) ~⚬ ((C1 |*| C2) |*| B12)

    def thenXI[B21, B22, C2, C3](
      that: XI[B1, B21, B22, C2, C3],
    )(using
      ev: B2 =:= (B21 |*| B22),
    ): (A1 |*| A2) ~⚬ (B21 |*| (C2 |*| C3))

    def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
      that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
    )(using
      ev1: B1 =:= (B11 |*| B12),
      ev2: B2 =:= (B21 |*| B22),
    ): (A1 |*| A2) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4))

    def assocLR_this_assocRL[X, Y1, Y2](h: AssocRL[X, B1, B2, Y1, Y2]): ((X |*| A1) |*| A2) ~⚬ ((Y1 |*| Y2) |*| B2)

    def assocLR_this_xi[X, Y2, Y3](h: XI[X, B1, B2, Y2, Y3]): ((X |*| A1) |*| A2) ~⚬ (B1 |*| (Y2 |*| Y3))

    def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, B1, B2, Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| A1) |*| A2) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4))

    def assocRL_this_assocLR[X, Y2, Y3](h: AssocLR[B1, B2, X, Y2, Y3]): (A1 |*| (A2 |*| X)) ~⚬ (B1 |*| (Y2 |*| Y3))

    def assocRL_this_ix[X, Y1, Y2](h: IX[B1, B2, X, Y1, Y2]): (A1 |*| (A2 |*| X)) ~⚬ ((Y1 |*| Y2) |*| B2)

    def assocRL_this_ixi[X1, X2, Y1, Y2, Y3, Y4](h: IXI[B1, B2, X1, X2, Y1, Y2, Y3, Y4]): (A1 |*| (A2 |*| (X1 |*| X2))) ~⚬ ((Y1 |*| Y2) |*| (Y3 |*| Y4))

    def ix_this_assocLR[X, Y2, Y3](that: AssocLR[B1, B2, X, Y2, Y3]): ((A1 |*| X) |*| A2) ~⚬ (B1 |*| (Y2 |*| Y3))

    def ix_this_ix[X, Y1, Y2](that: IX[B1, B2, X, Y1, Y2]): ((A1 |*| X) |*| A2) ~⚬ ((Y1 |*| Y2) |*| B2)

    def ix_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[B1, B2, P1, P2, Q1, Q2, Q3, Q4]): ((A1 |*| (P1 |*| P2)) |*| A2) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4))

    def xi_this_assocRL[X, Y1, Y2](g: AssocRL[X, B1, B2, Y1, Y2]): (A1 |*| (X |*| A2)) ~⚬ ((Y1 |*| Y2) |*| B2)

    def xi_this_xi[X, C2, C3](g: XI[X, B1, B2, C2, C3]): (A1 |*| (X |*| A2)) ~⚬ (B1 |*| (C2 |*| C3))

    def xi_this_ixi[P1, P2, C1, C2, C3, C4](g: IXI[P1, P2, B1, B2, C1, C2, C3, C4]): (A1 |*| ((P1 |*| P2) |*| A2)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4))

    def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
      g2: TransferOpt[P1, P2, Q1, Q2],
      that: AssocLR[B1, B2, Q1 |*| Q2, R2, R3],
    ): ((A1 |*| P1) |*| (A2 |*| P2)) ~⚬ (B1 |*| (R2 |*| R3))

    def ixi_fstThis_ix[P1, P2, Q1, Q2, R1, R2](
      g2: TransferOpt[P1, P2, Q1, Q2],
      that: IX[B1, B2, Q1 |*| Q2, R1, R2],
    ):((A1 |*| P1) |*| (A2 |*| P2)) ~⚬ ((R1 |*| R2) |*| B2) =
      UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_fstThis_ix")

    def ixi_sndThis_assocRL[P1, P2, Q1, Q2, R1, R2](
      g1: TransferOpt[P1, P2, Q1, Q2],
      that: AssocRL[Q1 |*| Q2, B1, B2, R1, R2],
    ): ((P1 |*| A1) |*| (P2 |*| A2)) ~⚬ ((R1 |*| R2) |*| B2)

    def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
      g1: TransferOpt[P1, P2, Q1, Q2],
      that: XI[Q1 |*| Q2, B1, B2, R2, R3],
    ): ((P1 |*| A1) |*| (P2 |*| A2)) ~⚬ (B1 |*| (R2 |*| R3))

    def invert: Xfer[B1, B2, ?, ?, A1, A2]

    protected def discardFst: ProjectProperRes[A1 |*| A2, B2]

    protected def discardSnd: ProjectProperRes[A1 |*| A2, B1]

    protected def projectFst[C1](p1: P.Proper[|*|, B1, C1]): ProjectProperRes[A1 |*| A2, C1 |*| B2]

    protected def projectSnd[C2](p2: P.Proper[|*|, B2, C2]): ProjectProperRes[A1 |*| A2, B1 |*| C2]

    final override def projectProper[C](p: P.Proper[|*|, B1 |*| B2, C]): ProjectProperRes[A1 |*| A2, C] =
      p.fromPair[B1, B2].switch[ProjectProperRes[A1 |*| A2, C]](
        caseDiscardFst = p2 => discardFst.project(p2),
        caseDiscardSnd = p1 => discardSnd.project(p1),
        casePar = [Q1, Q2] => (ev: C =:= (Q1 |*| Q2)) ?=> (p: P.Par[|*|, B1, B2, Q1, Q2]) =>
          ev match { case TypeEq(Refl()) =>
            p match {
              case P.Fst(p1)      => projectFst[Q1](p1).to[C]
              case P.Snd(p2)      => projectSnd[Q2](p2).to[C]
              case P.Both(p1, p2) => projectFst[Q1](p1).project[Q1 |*| Q2](p2.inSnd)
            }
          },
      )

    def >[C1, C2](that: Transfer[B1, B2, C1, C2]): (A1 |*| A2) ~⚬ (C1 |*| C2) =
      that after this

    def to[C1, C2](using ev: (B1 |*| B2) =:= (C1 |*| C2)): Transfer[A1, A2, C1, C2] = {
      val (ev1, ev2) = inj.unapply(ev)
      ev1.substituteCo[Transfer[A1, A2, _, C2]](ev2.substituteCo(this))
    }

    override def fold[->[_, _]](using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> (B1 |*| B2) = {
      import ev.*

      extension [X, Y, Z](f: X -> Y) {
        def >(g: Y -> Z): X -> Z =
          andThen(f, g)
      }

      this match {
        case Swap()                                 => swap
        case f: AssocLR[x1, x2, x3, y2, y3]         => assocLR[x1, x2, x3] > par(id, f.g.fold)
        case f: AssocRL[x1, x2, x3, y1, y2]         => assocRL[x1, x2, x3] > par(f.g.fold, id)
        case f: IX[x1, x2, x3, y1, y2]              => ix[x1, x2, x3] > par(f.g.fold, id)
        case f: XI[x1, x2, x3, y2, y3]              => xi[x1, x2, x3] > par(id, f.g.fold)
        case f: IXI[x1, x2, x3, x4, y1, y2, y3, y4] => ixi[x1, x2, x3, x4] > par(f.g1.fold, f.g2.fold)
      }
    }

    final override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A1 |*| A2)): ChaseFwRes[F, T, B1 |*| B2] =
      i match {
        case Focus.Id() =>
          ChaseFwRes.Split(ev)
        case fst: Focus.Fst[p, f1, a2] =>
          summon[(f1[T] |*| a2) =:= (A1 |*| A2)] match
            case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
              chaseFwFst[f1, T](fst.i)
        case snd: Focus.Snd[p, f2, a1] =>
          summon[(a1 |*| f2[T]) =:= (A1 |*| A2)] match
            case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
              chaseFwSnd[f2, T](snd.i)
      }

    final override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[T]): ChaseBwRes[A1 |*| A2, G, T] =
      i match {
        case Focus.Id() =>
          ChaseBwRes.Split(ev.flip)
        case i: Focus.Fst[pair, g1, b2] =>
          (ev andThen summon[G[T] =:= (g1[T] |*| b2)]) match
            case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
              chaseBwFst[g1, T](i.i)
        case i: Focus.Snd[pair, g2, b1] =>
          (ev andThen summon[G[T] =:= (b1 |*| g2[T])]) match
            case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
              chaseBwSnd[g2, T](i.i)
      }
  }

  object Transfer {
    case class Swap[X1, X2]() extends Transfer[X1, X2, X2, X1] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, X1, X2]): (Z1 |*| Z2) ~⚬ (X2 |*| X1) =
        that.thenSwap

      override protected def discardFst: ProjectProperRes[X1 |*| X2, X1] =
        ProjectProperRes.Projected(P.discardSnd, id[X1])

      override protected def discardSnd: ProjectProperRes[X1 |*| X2, X2] =
        ProjectProperRes.Projected(P.discardFst, id[X2])

      override protected def projectFst[C1](px2: Proper[|*|, X2, C1]): ProjectProperRes[X1 |*| X2, C1 |*| X1] =
        ProjectProperRes.Projected(px2.inSnd[X1], swap)

      override protected def projectSnd[C2](px1: Proper[|*|, X1, C2]): ProjectProperRes[X1 |*| X2, X2 |*| C2] =
        ProjectProperRes.Projected(px1.inFst[X2], swap)

      override def apply[F[_]](a: F[X1 |*| X2])(using F: Cartesian[|*|, F]): F[X2 |*| X1] = {
        val (x1, x2) = F.unzip(a)
        F.zip(x2, x1)
      }

      override def translateLR[<*>[_, _], F[_, _], S1, S2](
        fx1: F[X1, S1],
        fx2: F[X2, S2],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[T1] =>> Exists[[T2] =>> (tgt.TransferOpt[S1, S2, T1, T2], F[X2, T1], F[X1, T2])]] =
        Exists(Exists((tgt.Transfer.Swap[S1, S2](), fx2, fx1)))

      override def translateRL[<*>[_, _], F[_, _], T1, T2](
        fb1: F[X2, T1],
        fb2: F[X1, T2],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[S1] =>> Exists[[S2] =>> (F[X1, S1], F[X2, S2], tgt.TransferOpt[S1, S2, T1, T2])]] =
        Exists(Exists((fb2, fb1, tgt.Transfer.Swap())))

      override def chaseFwFst[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= X1): ChaseFwRes[[t] =>> F[t] |*| X2, T, X2 |*| X1] =
        ev match { case TypeEq(Refl()) =>
          ChaseFwRes.Transported[[t] =>> F[t] |*| X2, T, [t] =>> X2 |*| F[t], X2 |*| X1]([t] => (_: Unit) => swap[F[t], X2], i.inSnd, summon)
        }

      override def chaseFwSnd[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= X2): ChaseFwRes[[t] =>> X1 |*| F[t], T, X2 |*| X1] =
        ev match { case TypeEq(Refl()) =>
          ChaseFwRes.Transported[[t] =>> X1 |*| F[t], T, [t] =>> F[t] |*| X1, X2 |*| X1]([t] => (_: Unit) => swap[X1, F[t]], i.inFst, summon)
        }

      override def chaseBwFst[G[_], T](i: Focus[|*|, G])(using ev: X2 =:= G[T]): ChaseBwRes[X1 |*| X2, [t] =>> G[t] |*| X1, T] =
        ev match { case TypeEq(Refl()) =>
          ChaseBwRes.Transported[X1 |*| X2, [t] =>> X1 |*| G[t], [t] =>> G[t] |*| X1, T](summon, i.inSnd, [t] => (_: Unit) => swap[X1, G[t]])
        }

      override def chaseBwSnd[G[_], T](i: Focus[|*|, G])(using ev: X1 =:= G[T]): ChaseBwRes[X1 |*| X2, [t] =>> X2 |*| G[t], T] =
        ev match { case TypeEq(Refl()) =>
          ChaseBwRes.Transported[X1 |*| X2, [t] =>> G[t] |*| X2, [t] =>> X2 |*| G[t], T](summon, i.inFst, [t] => (_: Unit) => swap[G[t], X2])
        }

      override def thenBi[C1, C2](g1: X2 ~⚬ C1, g2: X1 ~⚬ C2): Xfer[X1, X2, ?, ?, C1, C2] =
        Xfer(g2, g1, Swap())

      override def thenSwap: (X1 |*| X2) ~⚬ (X1 |*| X2) =
        Id()

      override def thenAssocLR[X21, X22, C2, C3](
        that: AssocLR[X21, X22, X1, C2, C3],
      )(using
        ev: X2 =:= (X21 |*| X22),
      ): (X1 |*| X2) ~⚬ (X21 |*| (C2 |*| C3)) = {
        ev match { case TypeEq(Refl()) => xi[X1, X21, X22] > snd(swap > that.g.asShuffle) }
      }

      override def thenAssocRL[X11, X12, C1, C2](
        that: AssocRL[X2, X11, X12, C1, C2],
      )(using
        ev: X1 =:= (X11 |*| X12),
      ): (X1 |*| X2) ~⚬ ((C1 |*| C2) |*| X12) =
        ev match { case TypeEq(Refl()) => ix[X11, X12, X2] > fst(swap > that.g.asShuffle) }

      override def thenIX[B11, B12, C1, C2](
        that: IX[B11, B12, X1, C1, C2],
      )(using
        ev: X2 =:= (B11 |*| B12),
      ): (X1 |*| X2) ~⚬ ((C1 |*| C2) |*| B12) =
        decompose(swap > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, Id0(ev) > fst(f2), AssocRL(h))
        }

      override def thenXI[X11, X12, C2, C3](
        that: XI[X2, X11, X12, C2, C3],
      )(using
        ev: X1 =:= (X11 |*| X12),
      ): (X1 |*| X2) ~⚬ (X11 |*| (C2 |*| C3)) =
        decompose(swap > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(Id0(ev) > snd(f1), f2, AssocLR(h))
        }

      override def thenIXI[B1, B2, B3, B4, C1, C2, C3, C4](
        that: IXI[B1, B2, B3, B4, C1, C2, C3, C4]
      )(using
        ev1: X2 =:= (B1 |*| B2),
        ev2: X1 =:= (B3 |*| B4),
      ): (X1 |*| X2) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        (decompose(that.g1.asShuffle after swap), decompose(that.g2.asShuffle after swap)) match
          case (Decomposition(f1, f2, h1), Decomposition(f3, f4, h2)) =>
            Xfer(par(f1, f3).from[X1], par(f2, f4).from[X2], IXI(h1, h2))

      override def assocLR_this_assocRL[X, Y1, Y2](h: AssocRL[X, X2, X1, Y1, Y2]): ((X |*| X1) |*| X2) ~⚬ ((Y1 |*| Y2) |*| X1) =
        IX[X, X1, X2, Y1, Y2](h.g).asShuffle

      override def assocLR_this_xi[X, Y2, Y3](h: XI[X, X2, X1, Y2, Y3]): ((X |*| X1) |*| X2) ~⚬ (X2 |*| (Y2 |*| Y3)) =
        Xfer(h.g.asShuffle, id, Swap())

      override def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, X2, X1, Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| X1) |*| X2) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        Xfer(assocLR > snd(that.g2.asShuffle), id, IX(that.g1))

      override def assocRL_this_assocLR[X, Y2, Y3](h: AssocLR[X2, X1, X, Y2, Y3]): (X1 |*| (X2 |*| X)) ~⚬ (X2 |*| (Y2 |*| Y3)) =
        XI(h.g).asShuffle

      override def assocRL_this_ix[X, Y1, Y2](h: IX[X2, X1, X, Y1, Y2]): (X1 |*| (X2 |*| X)) ~⚬ ((Y1 |*| Y2) |*| X1) =
        Xfer(id, h.g.asShuffle, Swap())

      override def assocRL_this_ixi[X3, X4, Y1, Y2, Y3, Y4](that: IXI[X2, X1, X3, X4, Y1, Y2, Y3, Y4]): (X1 |*| (X2 |*| (X3 |*| X4))) ~⚬ ((Y1 |*| Y2) |*| (Y3 |*| Y4)) =
        Xfer(id, AssocRL(that.g1).asShuffle, XI(that.g2))

      override def ix_this_assocLR[X, Y2, Y3](that: AssocLR[X2, X1, X, Y2, Y3]): ((X1 |*| X) |*| X2) ~⚬ (X2 |*| (Y2 |*| Y3)) =
        Xfer(that.g.asShuffle, id, Swap())

      override def ix_this_ix[X, Y1, Y2](that: IX[X2, X1, X, Y1, Y2]): ((X1 |*| X) |*| X2) ~⚬ ((Y1 |*| Y2) |*| X1) =
        decompose(swap > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(swap > fst(f1), f2, IX(h))
        }

      override def ix_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[X2, X1, P1, P2, Q1, Q2, Q3, Q4]): ((X1 |*| (P1 |*| P2)) |*| X2) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        decompose(swap > that.g1.asShuffle) match
          case Decomposition(f1, f2, h1) =>
            Xfer(xi > par(f1, that.g2.asShuffle), f2, IX(h1))

      override def xi_this_assocRL[X, Y1, Y2](g: AssocRL[X, X2, X1, Y1, Y2]): (X1 |*| (X |*| X2)) ~⚬ ((Y1 |*| Y2) |*| X1) =
        Xfer(Id(), g.g.asShuffle, Swap())

      override def xi_this_xi[X, C2, C3](g: XI[X, X2, X1, C2, C3]): (X1 |*| (X |*| X2)) ~⚬ (X2 |*| (C2 |*| C3)) =
        decompose(swap > g.g.asShuffle) match {
          case Decomposition(h1, h2, h) => Xfer(h1, fst(h2) > swap, XI(h))
        }

      override def xi_this_ixi[P1, P2, C1, C2, C3, C4](g: IXI[P1, P2, X2, X1, C1, C2, C3, C4]): (X1 |*| (P1 |*| P2 |*| X2)) ~⚬ (C1 |*| C2 |*| (C3 |*| C4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_ixi")

      override def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
        g2: TransferOpt[P1, P2, Q1, Q2],
        that: AssocLR[X2, X1, Q1 |*| Q2, R2, R3],
      ): ((X1 |*| P1) |*| (X2 |*| P2)) ~⚬ (X2 |*| (R2 |*| R3)) =
        decompose(AssocLR(g2).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, snd(f2), XI(h))
        }

      override def ixi_sndThis_assocRL[P1, P2, Q1, Q2, R1, R2](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: AssocRL[Q1 |*| Q2, X2, X1, R1, R2],
      ): ((P1 |*| X1) |*| (P2 |*| X2)) ~⚬ ((R1 |*| R2) |*| X1) =
        decompose(AssocRL(g1).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(fst(f1), f2, IX(h))
        }

      override def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: XI[Q1 |*| Q2, X2, X1, R2, R3],
      ): ((P1 |*| X1) |*| (P2 |*| X2)) ~⚬ (X2 |*| (R2 |*| R3)) =
        decompose(IX(g1).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, swap > snd(f2), XI(h))
        }

      override def invert: Xfer[X2, X1, ?, ?, X1, X2] =
        Xfer(Id(), Id(), Swap())

      override def ixiPairWith_:[A1, A2, A3, A4, B1, B2, B3, B4](
        that: Transfer.IXI[A1, A2, A3, A4, B1, B2, B3, B4],
      ): BiTransferOpt[A1 |*| A2, A3 |*| A4, X1, X2, B1 |*| B2, B3 |*| B4, X2, X1] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:(that)")

      override def nonePairWith_:[A1, A2](that: TransferOpt.None[A1, A2]): BiTransferOpt[A1, A2, X1, X2, A1, A2, X2, X1] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def swapPairWith_:[A1, A2](that: Transfer.Swap[A1, A2]): BiTransferOpt[A1, A2, X1, X2, A2, A1, X2, X1] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def pairWith[X3, X4, Z1, Z2](that: TransferOpt[X3, X4, Z1, Z2]): BiTransferOpt[X1, X2, X3, X4, X2, X1, Z1, Z2] =
        this swapPairWith_: that
    }

    case class AssocLR[A1, A2, A3, B2, B3](g: TransferOpt[A2, A3, B2, B3]) extends Transfer[A1 |*| A2, A3, A1, B2 |*| B3] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1 |*| A2, A3]): (Z1 |*| Z2) ~⚬ (A1 |*| (B2 |*| B3)) =
        that thenAssocLR this

      override protected def discardFst: ProjectProperRes[(A1 |*| A2) |*| A3, B2 |*| B3] =
        ProjectProperRes.Projected(P.Fst(P.discardFst), g.asShuffle)
      override protected def discardSnd: ProjectProperRes[(A1 |*| A2) |*| A3, A1] =
        ProjectProperRes.Projected(P.discardSnd(P.discardSnd), id[A1])

      override protected def projectFst[C1](p1: Proper[|*|, A1, C1]): ProjectProperRes[(A1 |*| A2) |*| A3, C1 |*| (B2 |*| B3)] =
        ProjectProperRes.Projected(p1.inFst[A2].inFst[A3], assocLR > snd(g.asShuffle))

      override protected def projectSnd[C2](p2: Proper[|*|, B2 |*| B3, C2]): ProjectProperRes[(A1 |*| A2) |*| A3, A1 |*| C2] =
        g.projectProper(p2) match {
          case ProjectProperRes.Projected(q, g1) =>
            def go[X](q: P.Proper[|*|, A2 |*| A3, X], g1: X ~⚬ C2): ProjectProperRes[(A1 |*| A2) |*| A3, A1 |*| C2] =
              q.fromPair[A2, A3].switch[ProjectProperRes[(A1 |*| A2) |*| A3, A1 |*| C2]](
                caseDiscardFst = q2 => ProjectProperRes.Projected(P.par1(P.discardSnd, q2), snd(g1)),
                caseDiscardSnd = q1 => ProjectProperRes.Projected(P.discardSnd(P.snd(q1)), snd(g1)),
                casePar = [P2, P3] => (ev1: X =:= (P2 |*| P3)) ?=> (q: P.Par[|*|, A2, A3, P2, P3]) =>           ev1 match { case TypeEq(Refl()) =>
                  q match
                    case P.Fst(q1)      => ProjectProperRes.Projected(q1.inSnd[A1].inFst[A3], assocLR > snd(g1))
                    case P.Snd(q2)      => ProjectProperRes.Projected(q2.inSnd[A1 |*| A2], assocLR > snd(g1))
                    case P.Both(q1, q2) => ProjectProperRes.Projected(P.Both(q1.inSnd[A1], q2), assocLR > snd(g1))
                },
              )

            go(q, g1)
        }

      override def apply[F[_]](a: F[(A1 |*| A2) |*| A3])(using F: Cartesian[|*|, F]): F[A1 |*| (B2 |*| B3)] = {
        val (a12, a3) = F.unzip(a)
        val (a1, a2)  = F.unzip(a12)
        F.zip(a1, g(F.zip(a2, a3)))
      }

      override def translateLR[<*>[_,_], F[_,_], S12, S3](
        fa12: F[A1 |*| A2, S12],
        fa3 : F[A3, S3],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[T1] =>> Exists[[T2] =>> (tgt.TransferOpt[S12, S3, T1, T2], F[A1, T1], F[B2 |*| B3, T2])]] = {
        m.unpair(fa12)                        match { case v @ m.Unpaired.Impl(fa1, fa2) =>
        g.translateLR(fa2, fa3)(m)            match { case e1 @ Exists.Some(e2 @ Exists.Some((g1, fb2, fb3))) =>
        Exists(Exists((tgt.Transfer.AssocLR[v.X1, v.X2, S3, e1.T, e2.T](g1), fa1, m.pair(fb2, fb3))))
        }}
      }

      override def translateRL[<*>[_, _], F[_, _], T1, T2](
        fa1: F[A1, T1],
        fb23: F[B2 |*| B3, T2],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[S1] =>> Exists[[S2] =>> (F[A1 |*| A2, S1], F[A3, S2], tgt.TransferOpt[S1, S2, T1, T2])]] = {
        m.unpair(fb23) match
          case m.Unpaired.Impl(fb2, fb3) =>
            g.translateRL(fb2, fb3)(m) match
              case Exists.Some(Exists.Some((fa2, fa3, h))) =>
                Exists(Exists((m.pair(fa1, fa2), fa3, tgt.Transfer.AssocLR(h))))
      }

      override def chaseFwFst[F[_], T](i: Focus[|*|, F])(using
        ev: F[T] =:= (A1 |*| A2),
      ): ChaseFwRes[[t] =>> F[t] |*| A3, T, A1 |*| (B2 |*| B3)] =
        i match {
          case Focus.Id() =>
            ChaseFwRes.Split(ev)
          case i: Focus.Fst[pair, f1, a2] =>
            (summon[(f1[T] |*| a2) =:= F[T]] andThen ev) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                ChaseFwRes.Transported[[t] =>> F[t] |*| A3, T, [t] =>> f1[t] |*| (B2 |*| B3), A1 |*| (B2 |*| B3)](
                  [t] => (_: Unit) => assocLR > snd(g.asShuffle),
                  i.i.inFst[B2 |*| B3],
                  summon,
                )
          case i: Focus.Snd[pair, f2, a1] =>
            (summon[(a1 |*| f2[T]) =:= F[T]] andThen ev) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                g.chaseFwFst[f2, T](i.i)
                  .inSnd[A1]
                  .after([t] => (_: Unit) => assocLR[A1, f2[t], A3])
        }

      override def chaseFwSnd[F[_], T](i: Focus[|*|, F])(using
        ev: F[T] =:= A3,
      ): ChaseFwRes[[t] =>> A1 |*| A2 |*| F[t], T, A1 |*| (B2 |*| B3)] =
        g.chaseFwSnd[F, T](i)
          .inSnd[A1]
          .after([t] => (_: Unit) => assocLR[A1, A2, F[t]])

      override def chaseBwFst[G[_], T](i: Focus[|*|, G])(using ev: A1 =:= G[T]): ChaseBwRes[(A1 |*| A2) |*| A3, [t] =>> G[t] |*| (B2 |*| B3), T] =
        ev match { case TypeEq(Refl()) =>
          ChaseBwRes.Transported[(A1 |*| A2) |*| A3, [t] =>> (G[t] |*| A2) |*| A3, [t] =>> G[t] |*| (B2 |*| B3), T](
            summon,
            i.inFst[A2].inFst[A3],
            [t] => (_: Unit) => assocLR > snd(g.asShuffle),
          )
        }

      override def chaseBwSnd[G[_], T](i: Focus[|*|, G])(using ev: (B2 |*| B3) =:= G[T]): ChaseBwRes[(A1 |*| A2) |*| A3, [t] =>> A1 |*| G[t], T] =
        g.chaseBw[G, T](i)(using ev).afterAssocLR[A1, A2, A3]

      override def thenBi[C1, C2](g1: A1 ~⚬ C1, g2: (B2 |*| B3) ~⚬ C2): Xfer[A1 |*| A2, A3, ?, ?, C1, C2] =
        decompose1(g.asShuffle > g2) match {
          case Decomposition1(f1, f2, g, ev) => ev.substituteCo(Xfer(par(g1, f1), f2, AssocLR(g)))
        }

      override def thenSwap: ((A1 |*| A2) |*| A3) ~⚬ ((B2 |*| B3) |*| A1) =
        Xfer(swap, id, IX(g))

      override def thenAssocLR[A11, A12, C2, C3](
        that: AssocLR[A11, A12, B2 |*| B3, C2, C3],
      )(using
        ev: A1 =:= (A11 |*| A12),
      ): ((A1 |*| A2) |*| A3) ~⚬ (A11 |*| (C2 |*| C3)) =
        ev match { case TypeEq(Refl()) =>
          decompose(assocLR > snd(g.asShuffle) > that.g.asShuffle) match
            case Decomposition(f1, f2, g) =>
              Xfer(assocLR[A11, A12, A2] > snd(f1), f2, AssocLR(g))
        }

      override def thenAssocRL[B21, B22, C1, C2](
        that: AssocRL[A1, B21, B22, C1, C2],
      )(using
        ev: (B2 |*| B3) =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ ((C1 |*| C2) |*| B22) =
        ev match {
          case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            TransferOpt.decompose(this.g) match
              case Right((i, j)) =>
                par(snd(i) > that.g.asShuffle, j)
              case Left(t) =>
                t.assocLR_this_assocRL(that)
        }

      override def thenIX[B11, B12, C1, C2](
        that: IX[B11, B12, B2 |*| B3, C1, C2],
      )(using
        ev: A1 =:= (B11 |*| B12),
      ): ((A1 |*| A2) |*| A3) ~⚬ ((C1 |*| C2) |*| B12) =
        decompose(AssocLR(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(fst(Id0(ev)) > ix > fst(f1), f2, IX(h))
        }

      override def thenXI[B21, B22, C2, C3](
        that: XI[A1, B21, B22, C2, C3],
      )(using
        ev: (B2 |*| B3) =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (B21 |*| (C2 |*| C3)) =
        ev match {
          case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            TransferOpt.decompose(this.g) match
              case Right((i, j)) =>
                Xfer(snd(i) > swap, j, AssocLR(that.g))
              case Left(t) =>
                t.assocLR_this_xi(that)
        }

      override def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
        that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
      )(using
        ev1: A1 =:= (B11 |*| B12),
        ev2: (B2 |*| B3) =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        fst(fst(Id0(ev1))) > (TransferOpt.decompose(ev2.biSubst(g)) match {
          case Right((i, j)) => Xfer(ix > fst(snd(i) > that.g1.asShuffle), j, AssocLR(that.g2))
          case Left(t)       => t.assocLR_this_ixi(that)
        })

      override def assocLR_this_assocRL[X, Y1, Y2](h: AssocRL[X, A1, B2 |*| B3, Y1, Y2]): ((X |*| (A1 |*| A2)) |*| A3) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        Xfer(AssocRL(h.g).asShuffle, Id(), AssocLR(g))

      override def assocLR_this_xi[X, Y2, Y3](h: XI[X, A1, B2 |*| B3, Y2, Y3]): ((X |*| (A1 |*| A2)) |*| A3) ~⚬ (A1 |*| (Y2 |*| Y3)) =
        decompose(assocLR > snd(g.asShuffle) > h.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(xi > snd(f1), f2, AssocLR(h))

      override def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, A1, B2 |*| B3, Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| (A1 |*| A2)) |*| A3) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_ixi")

      override def assocRL_this_assocLR[X, Y2, Y3](that: AssocLR[A1, B2 |*| B3, X, Y2, Y3]): ((A1 |*| A2) |*| (A3 |*| X)) ~⚬ (A1 |*| (Y2 |*| Y3)) =
        decompose(AssocRL(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(snd(f1), f2, AssocLR(h))
        }

      override def assocRL_this_ix[X, Y1, Y2](h: IX[A1, B2 |*| B3, X, Y1, Y2]): ((A1 |*| A2) |*| (A3 |*| X)) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        Xfer(id, swap, IXI(h.g, g))

      override def assocRL_this_ixi[X1, X2, Y1, Y2, Y3, Y4](h: IXI[A1, B2 |*| B3, X1, X2, Y1, Y2, Y3, Y4]): ((A1 |*| A2) |*| (A3 |*| (X1 |*| X2))) ~⚬ ((Y1 |*| Y2) |*| (Y3 |*| Y4)) =
        decompose(assocRL > fst(g.asShuffle) > h.g2.asShuffle) match {
          case Decomposition(f1, f2, g2) => Xfer(snd(f1), xi > snd(f2), IXI(h.g1, g2))
        }

      override def ix_this_assocLR[X, Y2, Y3](that: AssocLR[A1, B2 |*| B3, X, Y2, Y3]): (((A1 |*| A2) |*| X) |*| A3) ~⚬ (A1 |*| (Y2 |*| Y3)) =
        decompose(IX(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(assocLR > snd(f1), f2, AssocLR(h))
        }

      override def ix_this_ix[X, Y1, Y2](h: IX[A1, B2 |*| B3, X, Y1, Y2]): (((A1 |*| A2) |*| X) |*| A3) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        Xfer(IX(h.g).asShuffle, id, AssocLR(g))

      override def ix_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[A1, B2 |*| B3, P1, P2, Q1, Q2, Q3, Q4]): (((A1 |*| A2) |*| (P1 |*| P2)) |*| A3) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_ixi")

      override def xi_this_assocRL[X, Y1, Y2](h: AssocRL[X, A1, B2 |*| B3, Y1, Y2]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        decompose(swap > h.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(fst(f1), fst(f2), IXI(h, g))
        }

      override def xi_this_xi[X, C2, C3](that: XI[X, A1, B2 |*| B3, C2, C3]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ (A1 |*| (C2 |*| C3)) =
        decompose(xi > snd(g.asShuffle) > that.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(snd(f1), f2, AssocLR(h))

      override def xi_this_ixi[P1, P2, C1, C2, C3, C4](g: IXI[P1, P2, A1, B2 |*| B3, C1, C2, C3, C4]): (A1 |*| A2 |*| (P1 |*| P2 |*| A3)) ~⚬ (C1 |*| C2 |*| (C3 |*| C4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_ixi")

      override def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
        g2: TransferOpt[P1, P2, Q1, Q2],
        that: AssocLR[A1, B2 |*| B3, Q1 |*| Q2, R2, R3],
      ): (((A1 |*| A2) |*| P1) |*| (A3 |*| P2)) ~⚬ (A1 |*| (R2 |*| R3)) =
        decompose(ixi > par(g.asShuffle, g2.asShuffle) > that.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(assocLR > snd(f1), f2, AssocLR(h))

      override def ixi_sndThis_assocRL[P1, P2, Q1, Q2, R1, R2](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: AssocRL[Q1 |*| Q2, A1, B2 |*| B3, R1, R2],
      ): ((P1 |*| (A1 |*| A2)) |*| (P2 |*| A3)) ~⚬ ((R1 |*| R2) |*| (B2 |*| B3)) =
        decompose(IX(g1).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(assocRL > fst(f1), fst(f2), IXI(h, g))
        }

      override def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: XI[Q1 |*| Q2, A1, B2 |*| B3, R2, R3],
      ): ((P1 |*| (A1 |*| A2)) |*| (P2 |*| A3)) ~⚬ (A1 |*| (R2 |*| R3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_sndThis_xi")

      override def invert: Xfer[A1, B2 |*| B3, ?, ?, A1 |*| A2, A3] =
        Xfer(id, g.asShuffle.invert, AssocRL(TransferOpt.None()))

      override def ixiPairWith_:[X1, X2, X3, X4, Y1, Y2, Y3, Y4](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2, Y3, Y4],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1 |*| A2, A3, Y1 |*| Y2, Y3 |*| Y4, A1, B2 |*| B3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")

      override def nonePairWith_:[X1, X2](that: TransferOpt.None[X1, X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3, X1, X2, A1, B2 |*| B3] =
        BiTransferOpt.None_AssocLR[X1, X2, A1, A2, A3, B2, B3](this)

      override def swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3, X2, X1, A1, B2 |*| B3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def pairWith[X3, X4, Z1, Z2](that: TransferOpt[X3, X4, Z1, Z2]): BiTransferOpt[A1 |*| A2, A3, X3, X4, A1, B2 |*| B3, Z1, Z2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.pairWith($that)")
    }

    case class AssocRL[A1, A2, A3, B1, B2](g: TransferOpt[A1, A2, B1, B2]) extends Transfer[A1, A2 |*| A3, B1 |*| B2, A3] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1, A2 |*| A3]): (Z1 |*| Z2) ~⚬ ((B1 |*| B2) |*| A3) =
        that.thenAssocRL(this)

      override protected def discardFst: ProjectProperRes[A1 |*| (A2 |*| A3), A3] =
        ProjectProperRes.Projected(P.discardFst(P.discardFst), id[A3])

      override protected def discardSnd: ProjectProperRes[A1 |*| (A2 |*| A3), B1 |*| B2] =
        ProjectProperRes.Projected(P.Snd(P.discardSnd), g.asShuffle)

      override protected def projectFst[C1](p1: Proper[|*|, B1 |*| B2, C1]): ProjectProperRes[A1 |*| (A2 |*| A3), C1 |*| A3] =
        g.projectProper(p1) match {
          case ProjectProperRes.Projected(p0, f) =>
            def go[X](p0: P.Proper[|*|, A1 |*| A2, X], f: X ~⚬ C1): ProjectProperRes[A1 |*| (A2 |*| A3), C1 |*| A3] =
              p0.fromPair[A1, A2].switch(
                caseDiscardFst = p2 => ProjectProperRes.Projected(P.discardFst(P.fst(p2)), fst(f)),
                caseDiscardSnd = p1 => ProjectProperRes.Projected(P.par2(p1, P.discardFst), fst(f)),
                casePar = [Q1, Q2] => (ev: X =:= (Q1 |*| Q2)) ?=> (p: P.Par[|*|, A1, A2, Q1, Q2]) =>                    ev match { case TypeEq(Refl()) =>
                  p match
                    case P.Fst(p1)      => ProjectProperRes.Projected(p1.inFst[A2 |*| A3], assocRL > fst(f))
                    case P.Snd(p2)      => ProjectProperRes.Projected(p2.inFst[A3].inSnd[A1], assocRL > fst(f))
                    case P.Both(p1, p2) => ProjectProperRes.Projected(P.Both(p1, p2.inFst[A3]), assocRL > fst(f))
                },
              )

            go(p0, f)
        }

      override protected def projectSnd[C2](p2: Proper[|*|, A3, C2]): ProjectProperRes[A1 |*| (A2 |*| A3), B1 |*| B2 |*| C2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.projectSnd")

      override def apply[F[_]](a: F[A1 |*| (A2 |*| A3)])(using F: Cartesian[|*|, F]): F[(B1 |*| B2) |*| A3] = {
        val (a1, a23) = F.unzip(a)
        val (a2, a3)  = F.unzip(a23)
        F.zip(g(F.zip(a1, a2)), a3)
      }

      override def translateLR[<*>[_, _], F[_, _], S1, S23](
        fa1: F[A1, S1],
        fa23: F[A2 |*| A3, S23],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[T1] =>> Exists[[T2] =>> (tgt.TransferOpt[S1, S23, T1, T2], F[B1 |*| B2, T1], F[A3, T2])]] =
        m.unpair(fa23)                        match { case v @ m.Unpaired.Impl(fa2, fa3) =>
        g.translateLR(fa1, fa2)(m)            match { case e1 @ Exists.Some(e2 @ Exists.Some((g1, fb1, fb2))) =>
        Exists(Exists((tgt.Transfer.AssocRL[S1, v.X1, v.X2, e1.T, e2.T](g1), m.pair(fb1, fb2), fa3)))
        }}

      override def translateRL[<*>[_, _], F[_, _], T1, T2](
        fb12: F[B1 |*| B2, T1],
        fa3: F[A3, T2],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[S1] =>> Exists[[S2] =>> (F[A1, S1], F[A2 |*| A3, S2], tgt.TransferOpt[S1, S2, T1, T2])]] =
        m.unpair(fb12) match
          case m.Unpaired.Impl(fb1, fb2) =>
            g.translateRL(fb1, fb2)(m) match
              case Exists.Some(Exists.Some((fa1, fa2, h))) =>
                Exists(Exists((fa1, m.pair(fa2, fa3), tgt.Transfer.AssocRL(h))))

      override def chaseFwFst[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= A1): ChaseFwRes[[t] =>> F[t] |*| (A2 |*| A3), T, (B1 |*| B2) |*| A3] =
        ev match { case TypeEq(Refl()) =>
          g.chaseFw[[t] =>> F[t] |*| A2, T](i.inFst[A2])
            .inFst[A3]
            .after([t] => (_: Unit) => assocRL[F[t], A2, A3])
        }

      override def chaseFwSnd[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A2 |*| A3)): ChaseFwRes[[t] =>> A1 |*| F[t], T, (B1 |*| B2) |*| A3] =
        i match {
          case Focus.Id() =>
            ChaseFwRes.Split(ev)
          case i: Focus.Fst[pair, f2, a3] =>
            (summon[(f2[T] |*| a3) =:= F[T]] andThen ev) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                g.chaseFw[[t] =>> A1 |*| f2[t], T](i.i.inSnd[A1])
                  .inFst[A3]
                  .after([t] => (_: Unit) => assocRL[A1, f2[t], A3])
          case i: Focus.Snd[pair, f3, a2] =>
            (summon[(a2 |*| f3[T]) =:= F[T]] andThen ev) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                ChaseFwRes.Transported[[t] =>> A1 |*| (A2 |*| f3[t]), T, [t] =>> (B1 |*| B2) |*| f3[t], (B1 |*| B2) |*| A3](
                  [t] => (_: Unit) => assocRL > fst(g.asShuffle),
                  i.i.inSnd[B1 |*| B2],
                  summon[((B1 |*| B2) |*| f3[T]) =:= ((B1 |*| B2) |*| A3)],
                )
        }

      override def chaseBwFst[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[T]): ChaseBwRes[A1 |*| (A2 |*| A3), [t] =>> G[t] |*| A3, T] =
        g.chaseBw[G, T](i).afterAssocRL

      override def chaseBwSnd[G[_], T](i: Focus[|*|, G])(using ev: A3 =:= G[T]): ChaseBwRes[A1 |*| (A2 |*| A3), [t] =>> (B1 |*| B2) |*| G[t], T] =
        ev match
          case TypeEq(Refl()) =>
            ChaseBwRes.Transported[A1 |*| (A2 |*| A3), [t] =>> A1 |*| (A2 |*| G[t]), [t] =>> (B1 |*| B2) |*| G[t], T](
              summon,
              i.inSnd[A2].inSnd[A1],
              [t] => (_: Unit) => assocRL[A1, A2, G[t]] > fst(g.asShuffle),
            )

      override def thenBi[C1, C2](g1: (B1 |*| B2) ~⚬ C1, g2: A3 ~⚬ C2): Xfer[A1, A2 |*| A3, ?, ?, C1, C2] =
        decompose1(g.asShuffle > g1) match {
          case Decomposition1(f1, f2, h, ev) => ev.substituteCo[Xfer[A1, A2 |*| A3, ?, ?, _, C2]](Xfer(f1, par(f2, g2), AssocRL(h)))
        }

      override def thenSwap: (A1 |*| (A2 |*| A3)) ~⚬ (A3 |*| (B1 |*| B2)) =
        decompose(g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, fst(f2) > swap, XI(h))
        }

      override def thenAssocLR[D1, D2, C2, C3](
        that: AssocLR[D1, D2, A3, C2, C3],
      )(using
        ev: (B1 |*| B2) =:= (D1 |*| D2),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (D1 |*| (C2 |*| C3)) =
        ev match {
          case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            TransferOpt.decompose(this.g) match
              case Right((i, j)) =>
                par(i, fst(j) > that.g.asShuffle)
              case Left(t) =>
                t.assocRL_this_assocLR(that)
        }

      override def thenAssocRL[B3, B4, C1, C2](
        that: AssocRL[B1 |*| B2, B3, B4, C1, C2],
      )(using
        ev: A3 =:= (B3 |*| B4),
      ): (A1 |*| (A2 |*| A3)) ~⚬ ((C1 |*| C2) |*| B4) =
        decompose(AssocRL(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, snd(Id0(ev)) > assocRL > fst(f2), AssocRL(h))
        }

      override def thenIX[B11, B12, C1, C2](
        that: IX[B11, B12, A3, C1, C2],
      )(using
        ev: (B1 |*| B2) =:= (B11 |*| B12),
      ): (A1 |*| (A2 |*| A3)) ~⚬ ((C1 |*| C2) |*| B12) =
        TransferOpt.decompose(ev.biSubst(g)) match {
          case Right((i, j)) => Xfer(i, fst(j) > swap, AssocRL(that.g))
          case Left(t)       => t.assocRL_this_ix(that)
        }

      override def thenXI[A31, A32, C2, C3](
        that: XI[B1 |*| B2, A31, A32, C2, C3],
      )(using
        ev: A3 =:= (A31 |*| A32),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (A31 |*| (C2 |*| C3)) =
        decompose(assocRL > fst(g.asShuffle) > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) =>
            Xfer(f1, snd(id[A3].to[A31 |*| A32]) > xi > snd(f2), XI(h))
        }

      override def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
        that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
      )(using
        ev1: (B1 |*| B2) =:= (B11 |*| B12),
        ev2: A3 =:= (B21 |*| B22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) = {
        val thiz: AssocRL[A1, A2, A3, B11, B12] = ev1.biSubst(this)
        TransferOpt.decompose(thiz.g) match {
          case Right((i, j)) => Xfer(i, par(j, Id0(ev2)) > XI(that.g2).asShuffle, AssocRL(that.g1))
          case Left(t)       => snd(snd(Id0(ev2))) > t.assocRL_this_ixi(that)
        }
      }

      override def assocLR_this_assocRL[X, Y1, Y2](h: AssocRL[X, B1 |*| B2, A3, Y1, Y2]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ ((Y1 |*| Y2) |*| A3) =
        decompose(AssocLR(g).asShuffle > h.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, fst(f2), AssocRL(h))
        }

      override def assocLR_this_xi[X, Y2, Y3](h: XI[X, B1 |*| B2, A3, Y2, Y3]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        Xfer(swap, id, IXI(g, h.g))

      override def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, B1 |*| B2, A3, Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| A1) |*| (A2 |*| A3)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        decompose(assocLR > snd(g.asShuffle) > that.g1.asShuffle) match
          case Decomposition(f1, f2, h1) =>
            Xfer(ix > fst(f1), fst(f2), IXI(h1, that.g2))

      override def assocRL_this_assocLR[X, Y2, Y3](h: AssocLR[B1 |*| B2, A3, X, Y2, Y3]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        Xfer(id, AssocLR(h.g).asShuffle, AssocRL(g))

      override def assocRL_this_ix[X, Y1, Y2](that: IX[B1 |*| B2, A3, X, Y1, Y2]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ ((Y1 |*| Y2) |*| A3) =
        decompose(AssocRL(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, ix > fst(f2), AssocRL(h))
        }

      override def assocRL_this_ixi[X1, X2, Y1, Y2, Y3, Y4](h: IXI[B1 |*| B2, A3, X1, X2, Y1, Y2, Y3, Y4]): (A1 |*| ((A2 |*| A3) |*| (X1 |*| X2))) ~⚬ ((Y1 |*| Y2) |*| (Y3 |*| Y4)) =
        decompose(assocRL > fst(g.asShuffle) > h.g1.asShuffle) match
          case Decomposition(f1, f2, g1) =>
            Xfer(f1, ixi > par(f2, h.g2.asShuffle), AssocRL(g1))

      override def xi_this_assocRL[X, Y1, Y2](h: AssocRL[X, B1 |*| B2, A3, Y1, Y2]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ ((Y1 |*| Y2) |*| A3) =
        decompose(XI(g).asShuffle > h.g.asShuffle) match {
          case Decomposition(h1, h2, h) => Xfer(h1, assocRL > fst(h2), AssocRL(h))
        }

      override def ix_this_assocLR[X, Y2, Y3](that: AssocLR[B1 |*| B2, A3, X, Y2, Y3]): ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        decompose(swap > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(snd(f1), snd(f2), IXI(g, h))
        }

      override def ix_this_ix[X, Y1, Y2](that: IX[B1 |*| B2, A3, X, Y1, Y2]): ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ ((Y1 |*| Y2) |*| A3) =
        decompose(IX(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, fst(f2), AssocRL(h))
        }

      override def ix_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[B1 |*| B2, A3, P1, P2, Q1, Q2, Q3, Q4]): ((A1 |*| (P1 |*| P2)) |*| (A2 |*| A3)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        decompose(ix > fst(g.asShuffle) > that.g1.asShuffle) match
          case Decomposition(f1, f2, h1) =>
            decompose(swap > that.g2.asShuffle) match
              case Decomposition(f3, f4, h2) =>
                Xfer(assocRL > par(f1, f3), par(f2, f4), IXI(h1, h2))

      override def xi_this_xi[X, C2, C3](h: XI[X, B1 |*| B2, A3, C2, C3]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ ((B1 |*| B2) |*| (C2 |*| C3)) =
        Xfer(Id(), XI(h.g).asShuffle, AssocRL(g))

      override def xi_this_ixi[P1, P2, C1, C2, C3, C4](g: IXI[P1, P2, B1 |*| B2, A3, C1, C2, C3, C4]): (A1 |*| (P1 |*| P2 |*| (A2 |*| A3))) ~⚬ (C1 |*| C2 |*| (C3 |*| C4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_ixi")

      override def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
        g2: TransferOpt[P1, P2, Q1, Q2],
        that: AssocLR[B1 |*| B2, A3, Q1 |*| Q2, R2, R3],
      ): ((A1 |*| P1) |*| ((A2 |*| A3) |*| P2)) ~⚬ ((B1 |*| B2) |*| (R2 |*| R3)) =
        decompose(XI(g2).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(snd(f1), assocLR > snd(f2), IXI(g, h))
        }

      override def ixi_sndThis_assocRL[P1, P2, Q1, Q2, R1, R2](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: AssocRL[Q1 |*| Q2, B1 |*| B2, A3, R1, R2],
      ): ((P1 |*| A1) |*| (P2 |*| (A2 |*| A3))) ~⚬ ((R1 |*| R2) |*| A3) =
        decompose(ixi > par(g1.asShuffle, g.asShuffle) > that.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(f1, assocRL > fst(f2), AssocRL(h))

      override def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: XI[Q1 |*| Q2, B1 |*| B2, A3, R2, R3],
      ): ((P1 |*| A1) |*| (P2 |*| (A2 |*| A3))) ~⚬ ((B1 |*| B2) |*| (R2 |*| R3)) =
        decompose(assocRL > fst(g1.asShuffle) > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(swap > snd(f1), xi > snd(f2), IXI(g, h))
        }

      override def invert: Xfer[B1 |*| B2, A3, ?, ?, A1, A2 |*| A3] =
        Xfer(g.asShuffle.invert, id, AssocLR(TransferOpt.None()))

      override def ixiPairWith_:[X1, X2, X3, X4, Y1, Y2, Y3, Y4](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2, Y3, Y4],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1, A2 |*| A3, Y1 |*| Y2, Y3 |*| Y4, B1 |*| B2, A3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")

      override def nonePairWith_:[X1, X2](that: TransferOpt.None[X1, X2]): BiTransferOpt[X1, X2, A1, A2 |*| A3, X1, X2, B1 |*| B2, A3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1, A2 |*| A3, X2, X1, B1 |*| B2, A3] =
        BiTransferOpt.Swap_AssocRL(that, this)

      override def pairWith[X3, X4, Z1, Z2](that: TransferOpt[X3, X4, Z1, Z2]): BiTransferOpt[A1, A2 |*| A3, X3, X4, B1 |*| B2, A3, Z1, Z2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.pairWith($that)")
    }

    case class IX[A1, A2, A3, B1, B2](g: TransferOpt[A1, A3, B1, B2]) extends Transfer[A1 |*| A2, A3, B1 |*| B2, A2] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1 |*| A2, A3]): (Z1 |*| Z2) ~⚬ ((B1 |*| B2) |*| A2) =
        that.thenIX(this)

      override protected def discardFst: ProjectProperRes[(A1 |*| A2) |*| A3, A2] =
        ProjectProperRes.Projected(P.discardSnd(P.discardFst), id[A2])

      override protected def discardSnd: ProjectProperRes[(A1 |*| A2) |*| A3, B1 |*| B2] =
        ProjectProperRes.Projected(P.Fst(P.discardSnd), g.asShuffle)

      override protected def projectFst[C1](p1: Proper[|*|, B1 |*| B2, C1]): ProjectProperRes[(A1 |*| A2) |*| A3, C1 |*| A2] =
        g.projectProper(p1) match
          case r @ ProjectProperRes.Projected(q, f) =>
            q.fromPair[A1, A3].switch(
              caseDiscardFst = q2 => ProjectProperRes.Projected(P.par1(P.discardFst, q2), swap > fst(f)),
              caseDiscardSnd = q1 => ProjectProperRes.Projected(P.discardSnd(P.fst(q1)), fst(f)),
              casePar = [Q1, Q2] => (ev: r.X =:= (Q1 |*| Q2)) ?=> (p: P.Par[|*|, A1, A3, Q1, Q2]) => {
                ev match { case TypeEq(Refl()) =>
                  p match
                    case P.Fst(p1)      => ProjectProperRes.Projected(p1.inFst[A2].inFst[A3], ix > fst(f))
                    case P.Snd(p2)      => ProjectProperRes.Projected(p2.inSnd[A1 |*| A2], ix > fst(f))
                    case P.Both(p1, p2) => ProjectProperRes.Projected(P.Both(p1.inFst[A2], p2), ix > fst(f))
                }
              },
            )


      override protected def projectSnd[C2](p2: Proper[|*|, A2, C2]): ProjectProperRes[(A1 |*| A2) |*| A3, (B1 |*| B2) |*| C2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.projectSnd")

      override def apply[F[_]](a: F[(A1 |*| A2) |*| A3])(using F: Cartesian[|*|, F]): F[(B1 |*| B2) |*| A2] = {
        val (a12, a3) = F.unzip(a)
        val (a1, a2)  = F.unzip(a12)
        F.zip(g(F.zip(a1, a3)), a2)
      }

      override def translateLR[<*>[_, _], F[_, _], S12, S3](
        fa12: F[A1 |*| A2, S12],
        fa3: F[A3, S3],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[T1] =>> Exists[[T2] =>> (tgt.TransferOpt[S12, S3, T1, T2], F[B1 |*| B2, T1], F[A2, T2])]] =
        m.unpair(fa12) match
          case v @ m.Unpaired.Impl(fa1, fa2) =>
            g.translateLR(fa1, fa3)(m) match
              case e1 @ Exists.Some(e2 @ Exists.Some((g1, fb1, fb2))) =>
                Exists(Exists((tgt.Transfer.IX[v.X1, v.X2, S3, e1.T, e2.T](g1), m.pair(fb1, fb2), fa2)))

      override def translateRL[<*>[_, _], F[_, _], T1, T2](
        fb12: F[B1 |*| B2, T1],
        fa2: F[A2, T2],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[S1] =>> Exists[[S2] =>> (F[A1 |*| A2, S1], F[A3, S2], tgt.TransferOpt[S1, S2, T1, T2])]] =
        m.unpair(fb12) match
          case m.Unpaired.Impl(fb1, fb2) =>
            g.translateRL(fb1, fb2)(m) match
              case Exists.Some(Exists.Some((fa1, fa3, g1))) =>
                Exists(Exists((m.pair(fa1, fa2), fa3, tgt.Transfer.IX(g1))))

      override def chaseFwFst[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A1 |*| A2)): ChaseFwRes[[t] =>> F[t] |*| A3, T, (B1 |*| B2) |*| A2] =
        ev match { case TypeEq(Refl()) =>
          i match
            case Focus.Id() =>
              ChaseFwRes.Split(ev)
            case i: Focus.Fst[pair, f1, a2] =>
              summon[(f1[T] |*| a2) =:= (A1 |*| A2)] match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                g.chaseFw[[t] =>> f1[t] |*| A3, T](i.i.inFst[A3])
                  .inFst[A2]
                  .after([t] => (_: Unit) => ix[f1[t], A2, A3])
              }
            case i: Focus.Snd[pair, f2, a1] =>
              summon[(a1 |*| f2[T]) =:= (A1 |*| A2)] match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                ChaseFwRes.Transported[[t] =>> F[t] |*| A3, T, [t] =>> (B1 |*| B2) |*| f2[t], (B1 |*| B2) |*| A2](
                  [t] => (_: Unit) => ix[A1, f2[t], A3] > g.asShuffle.inFst[f2[t]],
                  i.i.inSnd[B1 |*| B2],
                  summon,
                )
              }
        }

      override def chaseFwSnd[F[_], T](i: Focus[|*|, F])(using F[T] =:= A3): ChaseFwRes[[t] =>> (A1 |*| A2) |*| F[t], T, (B1 |*| B2) |*| A2] =
        g.chaseFwSnd[F, T](i)
          .inFst[A2]
          .after([t] => (_: Unit) => ix[A1, A2, F[t]])

      override def chaseBwFst[G[_], T](i: Focus[|*|, G])(using (B1 |*| B2) =:= G[T]): ChaseBwRes[(A1 |*| A2) |*| A3, [t] =>> G[t] |*| A2, T] =
        g.chaseBw[G, T](i).afterIX

      override def chaseBwSnd[G[_], T](i: Focus[|*|, G])(using ev: A2 =:= G[T]): ChaseBwRes[(A1 |*| A2) |*| A3, [t] =>> (B1 |*| B2) |*| G[t], T] =
        ev match { case TypeEq(Refl()) =>
          ChaseBwRes.Transported[(A1 |*| A2) |*| A3, [t] =>> (A1 |*| G[t]) |*| A3, [t] =>> (B1 |*| B2) |*| G[t], T](
            summon,
            i.inSnd[A1].inFst[A3],
            [t] => (_: Unit) => ix[A1, G[t], A3] > fst(g.asShuffle),
          )
        }

      override def thenBi[C1, C2](g1: (B1 |*| B2) ~⚬ C1, g2: A2 ~⚬ C2): Xfer[A1 |*| A2, A3, ?, ?, C1, C2] =
        decompose1(g.asShuffle > g1) match {
          case Decomposition1(f1, f2, h, ev) => ev.substituteCo[Xfer[A1 |*| A2, A3, ?, ?, _, C2]](Xfer(par(f1, g2), f2, IX(h)))
        }

      override def thenSwap: ((A1 |*| A2) |*| A3) ~⚬ (A2 |*| (B1 |*| B2)) =
        Xfer(swap, id, AssocLR(g))

      override def thenAssocLR[D1, D2, C2, C3](
        that: AssocLR[D1, D2, A2, C2, C3],
      )(using
        ev: (B1 |*| B2) =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| A3) ~⚬ (D1 |*| (C2 |*| C3)) =
        TransferOpt.decompose(ev.biSubst(g)) match {
          case Right((i, j)) =>
            decompose(swap > that.g.asShuffle) match {
              case Decomposition(f1, f2, h) => Xfer(par(i, f1), j > f2, AssocLR(h))
            }
          case Left(t) =>
            t.ix_this_assocLR(that)
        }

      override def thenAssocRL[X1, X2, C1, C2](
        that: AssocRL[(B1 |*| B2), X1, X2, C1, C2],
      )(using
        ev: A2 =:= (X1 |*| X2),
      ): ((A1 |*| A2) |*| A3) ~⚬ ((C1 |*| C2) |*| X2) =
        ev match { case TypeEq(Refl()) =>
          decompose(IX(this.g).asShuffle > that.g.asShuffle) match
            case Decomposition(f1, f2, h) => Xfer(assocRL[A1, X1, X2] > fst(f1), f2, IX(h))
        }

      override def thenIX[B11, B12, C1, C2](
        that: IX[B11, B12, A2, C1, C2],
      )(using
        ev: (B1 |*| B2) =:= (B11 |*| B12),
      ): ((A1 |*| A2) |*| A3) ~⚬ ((C1 |*| C2) |*| B12) =
        TransferOpt.decompose(ev.biSubst(g)) match {
          case Right((i, j)) => par(fst(i) > that.g.asShuffle, j)
          case Left(t)       => t.ix_this_ix(that)
        }

      override def thenXI[A21, A22, C2, C3](
        that: XI[(B1 |*| B2), A21, A22, C2, C3],
      )(using
        ev: A2 =:= (A21 |*| A22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (A21 |*| (C2 |*| C3)) =
        decompose(IX(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(snd(Id0(ev)) > xi > snd(f1), f2, AssocLR(h))
        }

      override def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
        that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
      )(using
        ev1: (B1 |*| B2) =:= (B11 |*| B12),
        ev2: A2 =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ ((C1 |*|C2) |*| (C3 |*| C4)) =
        fst(snd(Id0(ev2))) > (TransferOpt.decompose(ev1.biSubst(g)) match {
          case Right((i, j)) =>
            decompose(swap > that.g2.asShuffle) match {
              case Decomposition(f1, f2, h) => Xfer(par(i, snd(f1)) > AssocRL(that.g1).asShuffle, j > f2, AssocLR(h))
            }
          case Left(t) =>
            t.ix_this_ixi(that)

        })

      override def assocLR_this_assocRL[X, Y1, Y2](h: AssocRL[X, (B1 |*| B2), A2, Y1, Y2]): ((X |*| (A1 |*| A2)) |*| A3) ~⚬ ((Y1 |*| Y2) |*| A2) =
        decompose(AssocLR(g).asShuffle > h.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(assocRL > fst(f1), f2, IX(h))
        }

      override def assocLR_this_xi[X, Y2, Y3](h: XI[X, (B1 |*| B2), A2, Y2, Y3]): ((X |*| (A1 |*| A2)) |*| A3) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        Xfer(XI(h.g).asShuffle, id, IX(g))

      override def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, (B1 |*| B2), A2, Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| (A1 |*| A2)) |*| A3) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        decompose(AssocLR(g).asShuffle > that.g1.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(ixi > par(f1, that.g2.asShuffle), f2, IX(h))
        }

      override def assocRL_this_assocLR[X, Y2, Y3](h: AssocLR[(B1 |*| B2), A2, X, Y2, Y3]): ((A1 |*| A2) |*| (A3 |*| X)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        IXI[A1, A2, A3, X, B1, B2, Y2, Y3](g, h.g).asShuffle

      override def assocRL_this_ix[X, Y1, Y2](h: IX[(B1 |*| B2), A2, X, Y1, Y2]): ((A1 |*| A2) |*| (A3 |*| X)) ~⚬ ((Y1 |*| Y2) |*| A2) =
        decompose(assocRL > fst(g.asShuffle) > h.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(fst(f1), f2, IX(h))
        }

      override def assocRL_this_ixi[X1, X2, Y1, Y2, Y3, Y4](h: IXI[(B1 |*| B2), A2, X1, X2, Y1, Y2, Y3, Y4]): ((A1 |*| A2) |*| (A3 |*| (X1 |*| X2))) ~⚬ ((Y1 |*| Y2) |*| (Y3 |*| Y4)) =
        decompose(assocRL > fst(g.asShuffle) > h.g1.asShuffle) match
          case Decomposition(f1, f2, h1) =>
            Xfer(fst(f1), assocRL > fst(f2), IXI(h1, h.g2))

      override def ix_this_assocLR[X, Y2, Y3](that: AssocLR[(B1 |*| B2), A2, X, Y2, Y3]): (((A1 |*| A2) |*| X) |*| A3) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        Xfer(AssocLR(that.g).asShuffle, id, IX(g))

      override def ix_this_ix[X, Y1, Y2](that: IX[(B1 |*| B2), A2, X, Y1, Y2]): (((A1 |*| A2) |*| X) |*| A3) ~⚬ ((Y1 |*| Y2) |*| A2) =
        decompose(IX(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(ix > fst(f1), f2, IX(h))
        }

      override def ix_this_ixi[P1, P2, Q1, Q2, Q3, Q4](
        that: IXI[B1 |*| B2, A2, P1, P2, Q1, Q2, Q3, Q4],
      ): (((A1 |*| A2) |*| (P1 |*| P2)) |*| A3) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        decompose(IX(g).asShuffle > that.g1.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(ixi > par(f1, that.g2.asShuffle), f2, IX(h))
        }

      override def xi_this_assocRL[X, Y1, Y2](h: AssocRL[X, (B1 |*| B2), A2, Y1, Y2]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ ((Y1 |*| Y2) |*| A2) =
        ix(XI(g).asShuffle > h.g.asShuffle)

      override def xi_this_xi[X, C2, C3](h: XI[X, (B1 |*| B2), A2, C2, C3]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ ((B1 |*| B2) |*| (C2 |*|C3)) =
        decompose(swap > h.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(snd(f1), swap > snd(f2), IXI(g, h))

      override def xi_this_ixi[P1, P2, C1, C2, C3, C4](h: IXI[P1, P2, B1 |*| B2, A2, C1, C2, C3, C4]): ((A1 |*| A2) |*| ((P1 |*| P2) |*| A3)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        decompose(xi > snd(g.asShuffle) > h.g1.asShuffle) match
          case Decomposition(f1, f2, h1) =>
            decompose(swap > h.g2.asShuffle) match
              case Decomposition(f3, f4, h2) =>
                Xfer(par(f1, f3), ix > par(f2, f4), IXI(h1, h2))

      override def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
        g2: TransferOpt[P1, P2, Q1, Q2],
        that: AssocLR[(B1 |*| B2), A2, Q1 |*| Q2, R2, R3],
      ): (((A1 |*| A2) |*| P1) |*| (A3 |*| P2)) ~⚬ ((B1 |*| B2) |*| (R2 |*| R3)) =
        decompose(AssocLR(g2).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(assocLR > snd(f1), snd(f2), IXI(g, h))
        }

      override def ixi_sndThis_assocRL[P1, P2, Q1, Q2, R1, R2](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: AssocRL[Q1 |*| Q2, (B1 |*| B2), A2, R1, R2],
      ): ((P1 |*| (A1 |*| A2)) |*| (P2 |*| A3)) ~⚬ ((R1 |*| R2) |*| A2) =
        decompose(ixi > par(g1.asShuffle, g.asShuffle) > that.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(assocRL > fst(f1), f2, IX(h))

      override def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: XI[Q1 |*| Q2, (B1 |*| B2), A2, R2, R3],
      ): ((P1 |*| (A1 |*| A2)) |*| (P2 |*| A3)) ~⚬ ((B1 |*| B2) |*| (R2 |*| R3)) =
        decompose(ix > fst(g1.asShuffle) > that.g.asShuffle) match
          case Decomposition(f1, f2, h) => Xfer(xi > snd(f1), swap > snd(f2), IXI(g, h))

      override def invert: Xfer[(B1 |*| B2), A2, ?, ?, A1 |*| A2, A3] =
        Xfer(g.asShuffle.invert, id, IX(TransferOpt.None()))

      override def ixiPairWith_:[X1, X2, X3, X4, Y1, Y2, Y3, Y4](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2, Y3, Y4],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1 |*| A2, A3, Y1 |*| Y2, Y3 |*| Y4, (B1 |*| B2), A2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")

      override def nonePairWith_:[X1, X2](that: TransferOpt.None[X1, X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3, X1, X2, (B1 |*| B2), A2] =
        BiTransferOpt.None_IX(this)

      override def swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3, X2, X1, (B1 |*| B2), A2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def pairWith[X3, X4, Z1, Z2](that: TransferOpt[X3, X4, Z1, Z2]): BiTransferOpt[A1 |*| A2, A3, X3, X4, (B1 |*| B2), A2, Z1, Z2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.pairWith($that)")
    }

    case class XI[A1, A2, A3, B2, B3](g: TransferOpt[A1, A3, B2, B3]) extends Transfer[A1, A2 |*| A3, A2, B2 |*| B3] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1, A2 |*| A3]): (Z1 |*| Z2) ~⚬ (A2 |*| (B2 |*| B3)) =
        that thenXI this

      override protected def discardFst: ProjectProperRes[A1 |*| (A2 |*| A3), B2 |*| B3] =
        ProjectProperRes.Projected(P.Snd(P.discardFst), g.asShuffle)

      override protected def discardSnd: ProjectProperRes[A1 |*| (A2 |*| A3), A2] =
        ProjectProperRes.Projected(P.discardFst(P.discardSnd), id)

      override protected def projectFst[C1](p1: Proper[|*|, A2, C1]): ProjectProperRes[A1 |*| (A2 |*| A3), C1 |*| (B2 |*| B3)] =
        ProjectProperRes.Projected(P.Snd(P.Fst(p1)), XI(g).asShuffle)

      override protected def projectSnd[C2](p2: Proper[|*|, B2 |*| B3, C2]): ProjectProperRes[A1 |*| (A2 |*| A3), A2 |*| C2] =
        g.projectProper(p2) match {
          case ProjectProperRes.Projected(pa, g1) =>
            def go[X](pa: P.Proper[|*|, A1 |*| A3, X], g1: X ~⚬ C2): ProjectProperRes[A1 |*| (A2 |*| A3), A2 |*| C2] =
              pa.fromPair[A1, A3].switch[ProjectProperRes[A1 |*| (A2 |*| A3), A2 |*| C2]](
                caseDiscardFst = pa3 => ProjectProperRes.Projected(P.discardFst(P.snd(pa3)), snd(g1)),
                caseDiscardSnd = pa1 => ProjectProperRes.Projected(P.par2(pa1, P.discardSnd[|*|, A2, A3]), swap[X, A2] > snd(g1)),
                casePar = [q1, q3] => (ev: X =:= (q1 |*| q3)) ?=> (pa: P.Par[|*|, A1, A3, q1, q3]) =>                                   ev match { case TypeEq(Refl()) =>
                  pa match
                    case P.Fst(pa1) =>
                      ProjectProperRes.Projected(P.Fst(pa1), xi[q1, A2, A3] > snd(g1))
                    case P.Snd(pa3) =>
                      ProjectProperRes.Projected(P.Snd(P.Snd(pa3)), xi[A1, A2, q3] > snd(g1))
                    case P.Both(pa1, pa3) =>
                      ProjectProperRes.Projected(P.Both(pa1, P.Snd(pa3)), xi[q1, A2, q3] > snd(g1))
                },
              )

            go(pa, g1)
        }

      override def apply[F[_]](a: F[A1 |*| (A2 |*| A3)])(using F: Cartesian[|*|, F]): F[A2 |*| (B2 |*| B3)] = {
        val (a1, a23) = F.unzip(a)
        val (a2, a3)  = F.unzip(a23)
        F.zip(a2, g(F.zip(a1, a3)))
      }

      override def translateLR[<*>[_, _], F[_, _], S1, S23](
        fa1: F[A1, S1],
        fa23: F[A2 |*| A3, S23],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[T1] =>> Exists[[T2] =>> (tgt.TransferOpt[S1, S23, T1, T2], F[A2, T1], F[B2 |*| B3, T2])]] =
        m.unpair(fa23) match
          case v @ m.Unpaired.Impl(fa2, fa3) =>
            g.translateLR(fa1, fa3)(m) match
              case e1 @ Exists.Some(e2 @ Exists.Some((g1, fb2, fb3))) =>
                Exists(Exists((tgt.Transfer.XI[S1, v.X1, v.X2, e1.T, e2.T](g1), fa2, m.pair(fb2, fb3))))

      override def translateRL[<*>[_, _], F[_, _], T1, T2](
        fb1: F[A2, T1],
        fb23: F[B2 |*| B3, T2],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[S1] =>> Exists[[S2] =>> (F[A1, S1], F[A2 |*| A3, S2], tgt.TransferOpt[S1, S2, T1, T2])]] =
        m.unpair(fb23) match {
          case m.Unpaired.Impl(fb2, fb3) =>
            g.translateRL(fb2, fb3)(m) match
              case Exists.Some(Exists.Some((fa1, fa3, h))) =>
                Exists(Exists((fa1, m.pair(fb1, fa3), tgt.Transfer.XI(h))))
        }

      override def chaseFwFst[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= A1): ChaseFwRes[[t] =>> F[t] |*| (A2 |*| A3), T, A2 |*| (B2 |*| B3)] =
        ev match { case TypeEq(Refl()) =>
          ChaseFwRes.Transported[[t] =>> F[t] |*| (A2 |*| A3), T, [t] =>> A2 |*| (F[t] |*| A3), A2 |*| (F[T] |*| A3)](
            [t] => (_: Unit) => xi[F[t], A2, A3],
            i.inFst[A3].inSnd[A2],
            summon,
          ).thenSnd[A2, A1 |*| A3, B2 |*| B3](g.asShuffle)
        }

      override def chaseFwSnd[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A2 |*| A3)): ChaseFwRes[[t] =>> A1 |*| F[t], T, A2 |*| (B2 |*| B3)] =
        i match {
          case Focus.Id() =>
            ChaseFwRes.Split(ev)
          case i: Focus.Fst[pair, f1, z] =>
            (summon[(f1[T] |*| z) =:= F[T]] andThen ev)                                               match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
              type G[t] = A1 |*| (f1[t] |*| A3)
              type H[t] = f1[t] |*| (B2 |*| B3)
              ChaseFwRes.Transported[G, T, H, A2 |*| (B2 |*| B3)](
                [t] => (_: Unit) => xi[A1, f1[t], A3] > snd(g.asShuffle),
                i.i.inFst[B2 |*| B3],
                summon,
              )
            }
          case i: Focus.Snd[pair, f2, z] =>
            (summon[(z |*| f2[T]) =:= F[T]] andThen ev)                                               match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
              g.chaseFw[[x] =>> A1 |*| f2[x], T](i.i.inSnd[A1])
                .inSnd[A2]
                .after([x] => (_: Unit) => xi[A1, A2, f2[x]])
            }
        }

      override def chaseBwFst[G[_], T](i: Focus[|*|, G])(using ev: A2 =:= G[T]): ChaseBwRes[A1 |*| (A2 |*| A3), [t] =>> G[t] |*| (B2 |*| B3), T] =
        ev match { case TypeEq(Refl()) =>
          ChaseBwRes.Transported[A1 |*| (A2 |*| A3), [t] =>> A1 |*| (G[t] |*| A3), [t] =>> G[t] |*| (B2 |*| B3), T](
            summon,
            i.inFst[A3].inSnd[A1],
            [t] => (_: Unit) => XI[A1, G[t], A3, B2, B3](g).asShuffle,
          )
        }

      override def chaseBwSnd[G[_], T](i: Focus[|*|, G])(using ev: (B2 |*| B3) =:= G[T]): ChaseBwRes[A1 |*| (A2 |*| A3), [t] =>> A2 |*| G[t], T] =
        g.chaseBw[G, T](i).afterXI

      override def thenBi[C1, C2](g1: A2 ~⚬ C1, g2: (B2 |*| B3) ~⚬ C2): Xfer[A1, A2 |*| A3, ?, ?, C1, C2] =
        decompose1(g.asShuffle > g2) match {
          case Decomposition1(f1, f2, h, ev) => ev.substituteCo(Xfer(f1, par(g1, f2), XI(h)))
        }

      override def thenSwap: (A1 |*| (A2 |*| A3)) ~⚬ ((B2 |*| B3) |*| A2) =
        Xfer(Id(), swap, AssocRL(g))

      override def thenAssocLR[A21, A22, C2, C3](
        that: AssocLR[A21, A22, B2 |*| B3, C2, C3],
      )(using
        ev: A2 =:= (A21 |*| A22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (A21 |*| (C2 |*| C3)) =
        ev match { case TypeEq(Refl()) =>
          decompose(xi > snd(this.g.asShuffle) > that.g.asShuffle) match
            case Decomposition(f1, f2, g) =>
              Xfer(f1, assocLR[A21, A22, A3] > snd(f2), XI(g))
        }

      override def thenAssocRL[B2_, B3_, C1, C2](
        that: AssocRL[A2, B2_, B3_, C1, C2],
      )(using
        ev: (B2 |*| B3) =:= (B2_ |*| B3_),
      ): (A1 |*| (A2 |*| A3)) ~⚬ ((C1 |*| C2) |*| B3_) =
        ev match {
          case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            TransferOpt.decompose(this.g) match
              case Right((i, j)) =>
                decompose(swap > that.g.asShuffle) match
                  case Decomposition(f1, f2, h) =>
                    Xfer(i > f1, par(f2, j), AssocRL(h))
              case Left(t) =>
                t.xi_this_assocRL(that)
        }

      override def thenIX[A21, A22, C1, C2](
        that: IX[A21, A22, B2 |*| B3, C1, C2],
      )(using
        ev: A2 =:= (A21 |*| A22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ ((C1 |*| C2) |*| A22) =
        ev match { case TypeEq(Refl()) =>
          decompose(xi > snd(g.asShuffle) > that.g.asShuffle) match
            case Decomposition(f1, f2, h) =>
              Xfer(f1, ix[A21, A22, A3] > fst(f2), AssocRL(h))
        }

      override def thenXI[B2_, B3_, C2, C3](
        that: XI[A2, B2_, B3_, C2, C3],
      )(using
        ev: (B2 |*| B3) =:= (B2_ |*| B3_),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (B2_ |*| (C2 |*| C3)) =
        ev match {
          case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            TransferOpt.decompose(this.g) match
              case Right((i, j)) =>
                par(i, snd(j) > that.g.asShuffle)
              case Left(t) =>
                t.xi_this_xi(that)
        }

      override def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
        that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
      )(using
        ev1: A2 =:= (B11 |*| B12),
        ev2: (B2 |*| B3) =:= (B21 |*| B22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) = {
        def go(g: TransferOpt[A1, A3, B21, B22]): (A1 |*| ((B11 |*| B12) |*| A3)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
          TransferOpt.decompose(g) match {
            case Right((i, j)) =>
              decompose(swap > that.g1.asShuffle) match {
                case Decomposition(f1, f2, h) => Xfer(i > f1, Xfer(fst(f2), j, AssocLR(that.g2)), AssocRL(h))
              }
            case Left(t) =>
              t.xi_this_ixi(that)
          }

        ev1 match { case TypeEq(Refl()) =>
          ev2 match { case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            go(g)
          }
        }
      }

      override def assocLR_this_assocRL[X, Y1, Y2](h: AssocRL[X, A2, B2 |*| B3, Y1, Y2]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        IXI(h.g, g).asShuffle

      override def assocLR_this_xi[X, Y2, Y3](h: XI[X, A2, B2 |*| B3, Y2, Y3]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ (A2 |*| (Y2 |*| Y3)) =
        decompose(assocLR > snd(g.asShuffle) > h.g.asShuffle) match
          case Decomposition(f1, f2, h) => Xfer(f1, snd(f2), XI(h))

      override def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, A2, B2 |*| B3, Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| A1) |*| (A2 |*| A3)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        decompose(assocLR > snd(g.asShuffle) > that.g2.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(assocLR > snd(f1), snd(f2), IXI(that.g1, h))

      override def assocRL_this_assocLR[X, Y2, Y3](h: AssocLR[A2, B2 |*| B3, X, Y2, Y3]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ (A2 |*| (Y2 |*| Y3)) =
        decompose(assocRL > fst(g.asShuffle) > h.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, assocLR > snd(f2), XI(h))
        }

      override def assocRL_this_ix[X, Y1, Y2](h: IX[A2, B2 |*| B3, X, Y1, Y2]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        Xfer(id, IX(h.g).asShuffle, XI(g))

      override def assocRL_this_ixi[X1, X2, Y1, Y2, Y3, Y4](h: IXI[A2, B2 |*| B3, X1, X2, Y1, Y2, Y3, Y4]): (A1 |*| ((A2 |*| A3) |*| (X1 |*| X2))) ~⚬ ((Y1 |*| Y2) |*| (Y3 |*| Y4)) =
        decompose(assocRL > fst(g.asShuffle) > h.g2.asShuffle) match
          case Decomposition(f1, f2, h2) =>
            Xfer(f1, ixi > par(h.g1.asShuffle, f2), XI(h2))

      override def ix_this_assocLR[X, Y2, Y3](that: AssocLR[A2, B2 |*| B3, X, Y2, Y3]): ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ (A2 |*| (Y2 |*| Y3)) =
        decompose(IX(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, snd(f2), XI(h))
        }

      override def ix_this_ix[X, Y1, Y2](that: IX[A2, B2 |*| B3, X, Y1, Y2]): ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        decompose(swap > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(swap > fst(f1), fst(f2), IXI(h, g))
        }

      override def ix_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[A2, B2 |*| B3, P1, P2, Q1, Q2, Q3, Q4]): ((A1 |*| (P1 |*| P2)) |*| (A2 |*| A3)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        decompose(swap > that.g1.asShuffle) match
          case Decomposition(f1, f2, h1) =>
            decompose(ix > fst(g.asShuffle) > that.g2.asShuffle) match
              case Decomposition(f3, f4, h2) =>
                Xfer(xi > par(f1, f3), par(f2, f4), IXI(h1, h2))

      override def xi_this_assocRL[X, Y1, Y2](h: AssocRL[X, A2, B2 |*| B3, Y1, Y2]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        Xfer(Id(), AssocRL(h.g).asShuffle, XI(g))

      override def xi_this_xi[X, C2, C3](g: XI[X, A2, B2 |*| B3, C2, C3]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ (A2 |*| (C2 |*| C3)) =
        decompose(xi(this.g.asShuffle) > g.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, xi > snd(f2), XI(h))
        }

      override def xi_this_ixi[P1, P2, C1, C2, C3, C4](g: IXI[P1, P2, A2, B2 |*| B3, C1, C2, C3, C4]): (A1 |*| (P1 |*| P2 |*| (A2 |*| A3))) ~⚬ (C1 |*| C2 |*| (C3 |*| C4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_ixi")

      override def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
        g2: TransferOpt[P1, P2, Q1, Q2],
        that: AssocLR[A2, B2 |*| B3, Q1 |*| Q2, R2, R3],
      ): ((A1 |*| P1) |*| ((A2 |*| A3) |*| P2)) ~⚬ (A2 |*| (R2 |*| R3)) =
        decompose(ixi > par(g.asShuffle, g2.asShuffle) > that.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(f1, assocLR > snd(f2), XI(h))

      override def ixi_sndThis_assocRL[P1, P2, Q1, Q2, R1, R2](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: AssocRL[Q1 |*| Q2, A2, B2 |*| B3, R1, R2],
      ): ((P1 |*| A1) |*| (P2 |*| (A2 |*| A3))) ~⚬ ((R1 |*| R2) |*| (B2 |*| B3)) =
        decompose(assocRL > fst(g1.asShuffle) > that.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(fst(f1), assocRL > fst(f2), IXI(h, g))

      override def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: XI[Q1 |*| Q2, A2, B2 |*| B3, R2, R3],
      ): ((P1 |*| A1) |*| (P2 |*| (A2 |*| A3))) ~⚬ (A2 |*| (R2 |*| R3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_sndThis_xi")

      override def invert: Xfer[A2, B2 |*| B3, ?, ?, A1, A2 |*| A3] =
        Xfer(id, g.asShuffle.invert, XI(TransferOpt.None()))

      override def ixiPairWith_:[X1, X2, X3, X4, Y1, Y2, Y3, Y4](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2, Y3, Y4],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1, A2 |*| A3, Y1 |*| Y2, Y3 |*| Y4, A2, B2 |*| B3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")

      override def nonePairWith_:[X1, X2](that: TransferOpt.None[X1, X2]): BiTransferOpt[X1, X2, A1, A2 |*| A3, X1, X2, A2, B2 |*| B3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1, A2 |*| A3, X2, X1, A2, B2 |*| B3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def pairWith[X3, X4, Z1, Z2](that: TransferOpt[X3, X4, Z1, Z2]): BiTransferOpt[A1, A2 |*| A3, X3, X4, A2, B2 |*| B3, Z1, Z2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.pairWith($that)")
    }

    case class IXI[A1, A2, A3, A4, B1, B2, B3, B4](
      g1: TransferOpt[A1, A3, B1, B2],
      g2: TransferOpt[A2, A4, B3, B4],
    ) extends Transfer[A1 |*| A2, A3 |*| A4, B1 |*| B2, B3 |*| B4] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1 |*| A2, A3 |*| A4]): (Z1 |*| Z2) ~⚬ ((B1 |*| B2) |*| (B3 |*| B4)) =
        that thenIXI this

      override protected def discardFst: ProjectProperRes[(A1 |*| A2) |*| (A3 |*| A4), B3 |*| B4] =
        ProjectProperRes.Projected(P.Both(P.discardFst, P.discardFst), g2.asShuffle)

      override protected def discardSnd: ProjectProperRes[(A1 |*| A2) |*| (A3 |*| A4), B1 |*| B2] =
        ProjectProperRes.Projected(P.Both(P.discardSnd, P.discardSnd), g1.asShuffle)

      override protected def projectFst[C1](p1: Proper[|*|, B1 |*| B2, C1]): ProjectProperRes[(A1 |*| A2) |*| (A3 |*| A4), C1 |*| (B3 |*| B4)] =
        g1.projectProper(p1) match {
          case r @ ProjectProperRes.Projected(q, f1) =>
            q.fromPair[A1, A3].switch(
              caseDiscardFst = q2 => ProjectProperRes.Projected(P.par1(P.discardFst, q2.inFst[A4]), xi > par(f1, g2.asShuffle)),
              caseDiscardSnd = q1 => ProjectProperRes.Projected(P.par2(q1.inFst[A2], P.discardFst), assocLR > par(f1, g2.asShuffle)),
              casePar = [Q1, Q2] => (ev: r.X =:= (Q1 |*| Q2)) ?=> (p: P.Par[|*|, A1, A3, Q1, Q2]) =>                                    ev match { case TypeEq(Refl()) =>
                p match
                  case P.Fst(p1)      => ProjectProperRes.Projected(p1.inFst[A2].inFst[A3 |*| A4], ixi > par(f1, g2.asShuffle))
                  case P.Snd(p2)      => ProjectProperRes.Projected(p2.inFst[A4].inSnd[A1 |*| A2], ixi > par(f1, g2.asShuffle))
                  case P.Both(p1, p2) => ProjectProperRes.Projected(P.Both(p1.inFst[A2], p2.inFst[A4]), ixi > par(f1, g2.asShuffle))
              },
            )
        }

      override protected def projectSnd[C2](p2: Proper[|*|, B3 |*| B4, C2]): ProjectProperRes[(A1 |*| A2) |*| (A3 |*| A4), (B1 |*| B2) |*| C2] =
        g2.projectProper(p2) match {
          case r @ ProjectProperRes.Projected(q, f2) =>
            q.fromPair[A2, A4].switch(
              caseDiscardFst = q2 => ProjectProperRes.Projected(P.par1(P.discardSnd, q2.inSnd[A3]), assocRL > par(g1.asShuffle, f2)),
              caseDiscardSnd = q1 => ProjectProperRes.Projected(P.par2(q1.inSnd[A1], P.discardSnd), ix > par(g1.asShuffle, f2)),
              casePar = [Q1, Q2] => (ev: r.X =:= (Q1 |*| Q2)) ?=> (p: P.Par[|*|, A2, A4, Q1, Q2]) => ev match { case TypeEq(Refl()) =>
                p match
                  case P.Fst(p1)      => ProjectProperRes.Projected(p1.inSnd[A1].inFst[A3 |*| A4], ixi > par(g1.asShuffle, f2))
                  case P.Snd(p2)      => ProjectProperRes.Projected(p2.inSnd[A3].inSnd[A1 |*| A2], ixi > par(g1.asShuffle, f2))
                  case P.Both(p1, p2) => ProjectProperRes.Projected(P.Both(p1.inSnd[A1], p2.inSnd[A3]), ixi > par(g1.asShuffle, f2))
              },
            )
        }

      override def apply[F[_]](a: F[(A1 |*| A2) |*| (A3 |*| A4)])(using F: Cartesian[|*|, F]): F[(B1 |*| B2) |*| (B3 |*| B4)] = {
        val (a12, a34) = F.unzip(a)
        val (a1, a2)   = F.unzip(a12)
        val (a3, a4)   = F.unzip(a34)
        F.zip(g1(F.zip(a1, a3)), g2(F.zip(a2, a4)))
      }

      override def translateLR[<*>[_, _], F[_, _], S1, S2](
        fa12: F[A1 |*| A2, S1],
        fa34: F[A3 |*| A4, S2],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[T1] =>> Exists[[T2] =>> (tgt.TransferOpt[S1, S2, T1, T2], F[B1 |*| B2, T1], F[B3 |*| B4, T2])]] =
        m.unpair(fa12)                match { case m.Unpaired.Impl(fa1, fa2) =>
        m.unpair(fa34)                match { case m.Unpaired.Impl(fa3, fa4) =>
        g1.translateLR(fa1, fa3)(m)   match { case Exists.Some(Exists.Some((h1, fb1, fb2))) =>
        g2.translateLR(fa2, fa4)(m)   match { case Exists.Some(Exists.Some((h2, fb3, fb4))) =>
        Exists(Exists((
          tgt.Transfer.IXI(h1, h2),
          m.pair(fb1, fb2),
          m.pair(fb3, fb4),
        )))
        }}}}

      override def translateRL[<*>[_, _], F[_, _], T1, T2](
        fb12: F[B1 |*| B2, T1],
        fb34: F[B3 |*| B4, T2],
      )(
        m: SemigroupalObjectMap[|*|, <*>, F],
      )(using
        tgt: Shuffle[<*>],
      ): Exists[[S1] =>> Exists[[S2] =>> (F[A1 |*| A2, S1], F[A3 |*| A4, S2], tgt.TransferOpt[S1, S2, T1, T2])]] =
        m.unpair(fb12) match
          case m.Unpaired.Impl(fb1, fb2) =>
            m.unpair(fb34) match
              case m.Unpaired.Impl(fb3, fb4) =>
                g1.translateRL(fb1, fb2)(m) match
                  case Exists.Some(Exists.Some((fa1, fa3, h1))) =>
                    g2.translateRL(fb3, fb4)(m) match
                      case Exists.Some(Exists.Some((fa2, fa4, h2))) =>
                        Exists(Exists((m.pair(fa1, fa2), m.pair(fa3, fa4), tgt.Transfer.IXI(h1, h2))))

      override def chaseFwFst[F[_], T](i: Focus[|*|, F])(using
        ev: F[T] =:= (A1 |*| A2),
      ): ChaseFwRes[[t] =>> F[t] |*| (A3 |*| A4), T, B1 |*| B2 |*| (B3 |*| B4)] =
        i match {
          case Focus.Id() =>
            ChaseFwRes.Split(ev)
          case i: Focus.Fst[pair, f1, a2] =>
            (summon[(f1[T] |*| a2) =:= F[T]] andThen ev) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                g1.chaseFwFst[f1, T](i.i)
                  .inFst(g2.asShuffle)
                  .after([t] => (_: Unit) => ixi[f1[t], A2, A3, A4])
          case i: Focus.Snd[pair, f2, a1] =>
            (summon[(a1 |*| f2[T]) =:= F[T]] andThen ev) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                g2.chaseFwFst[f2, T](i.i)
                  .inSnd(g1.asShuffle)
                  .after([t] => (_: Unit) => ixi[A1, f2[t], A3, A4])
        }

      override def chaseFwSnd[F[_], T](i: Focus[|*|, F])(using
        ev: F[T] =:= (A3 |*| A4),
      ): ChaseFwRes[[t] =>> A1 |*| A2 |*| F[t], T, B1 |*| B2 |*| (B3 |*| B4)] =
        i match {
          case Focus.Id() =>
            ChaseFwRes.Split(ev)
          case i: Focus.Fst[pair, f1, a4] =>
            (summon[(f1[T] |*| a4) =:= F[T]] andThen ev) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                g1.chaseFwSnd[f1, T](i.i)
                  .inFst(g2.asShuffle)
                  .after([t] => (_: Unit) => ixi[A1, A2, f1[t], A4])
          case i: Focus.Snd[pair, f2, a3] =>
            (summon[(a3 |*| f2[T]) =:= F[T]] andThen ev) match
              case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
                g2.chaseFwSnd[f2, T](i.i)
                  .inSnd(g1.asShuffle)
                  .after([t] => (_: Unit) => ixi[A1, A2, A3, f2[t]])
        }

      override def chaseBwFst[G[_], T](i: Focus[|*|, G])(using (B1 |*| B2) =:= G[T]): ChaseBwRes[A1 |*| A2 |*| (A3 |*| A4), [t] =>> G[t] |*| (B3 |*| B4), T] =
        g1.chaseBw[G, T](i)
          .afterIXI1[A1, A2, A3, A4]
          .andThen[[t] =>> G[t] |*| (B3 |*| B4)]([t] => (_: Unit) => snd(g2.asShuffle))

      override def chaseBwSnd[G[_], T](i: Focus[|*|, G])(using (B3 |*| B4) =:= G[T]): ChaseBwRes[A1 |*| A2 |*| (A3 |*| A4), [t] =>> B1 |*| B2 |*| G[t], T] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.chaseBwSnd($i)")

      override def thenBi[C1, C2](h1: (B1 |*| B2) ~⚬ C1, h2: (B3 |*| B4) ~⚬ C2): Xfer[A1 |*| A2, A3 |*| A4, ?, ?, C1, C2] =
        (decompose1(g1.asShuffle > h1), decompose1(g2.asShuffle > h2)) match {
          case (Decomposition1(g11, g12, h1, TypeEq(Refl())), Decomposition1(g21, g22, h2, TypeEq(Refl()))) =>
            Xfer(par(g11, g21), par(g12, g22), IXI(h1, h2))
        }

      override def thenSwap: ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ ((B3 |*| B4) |*| (B1 |*| B2)) =
        Xfer(swap, swap, IXI(g2, g1))

      override def thenAssocLR[D1, D2, C2, C3](
        that: AssocLR[D1, D2, B3 |*| B4, C2, C3],
      )(using
        ev: (B1 |*| B2) =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (D1 |*| (C2 |*| C3)) = {
        val thiz = ev.biSubst[IXI[A1, A2, A3, A4, _, _, B3, B4]](this)
        TransferOpt.decompose(thiz.g1) match {
          case Right((i, j)) =>
            decompose(XI(thiz.g2).asShuffle > that.g.asShuffle) match {
              case Decomposition(f1, f2, h) => Xfer(par(i, f1), fst(j) > f2, AssocLR(h))
            }
          case Left(t) =>
            t.ixi_fstThis_assocLR(thiz.g2, that)
        }
      }

      override def thenAssocRL[D1, D2, C1, C2](
        that: AssocRL[(B1 |*| B2), D1, D2, C1, C2],
      )(using
        ev: (B3 |*| B4) =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ ((C1 |*| C2) |*| D2) =
        TransferOpt.decompose(ev.biSubst(g2)) match {
          case Right((i, j)) =>
            decompose(ix > par(g1.asShuffle, i) > that.g.asShuffle) match {
              case Decomposition(f1, f2, h) => Xfer(f1, par(f2, j), AssocRL(h))
            }
          case Left(t) =>
            t.ixi_sndThis_assocRL(g1, that)
        }

      override def thenIX[B1_, B2_, C1, C2](
        that: IX[B1_, B2_, B3 |*| B4, C1, C2],
      )(using
        ev: (B1 |*| B2) =:= (B1_ |*| B2_),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ ((C1 |*| C2) |*| B2_) =
        ev match
          case BiInjective[|*|](TypeEq(Refl()), TypeEq(Refl())) =>
            TransferOpt.decompose(g1) match {
              case Right((i, j)) =>
                decompose(assocLR > snd(g2.asShuffle) > that.g.asShuffle) match
                  case Decomposition(f1, f2, h) =>
                    Xfer(fst(i) > f1, swap > par(f2, j), AssocRL(h))
              case Left(t) =>
                t.ixi_fstThis_ix(g2, that)
            }

      override def thenXI[D1, D2, C2, C3](
        that: XI[(B1 |*| B2), D1, D2, C2, C3],
      )(using
        ev: (B3 |*| B4) =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (D1 |*| (C2 |*| C3)) = {
        val thiz = ev.biSubst[IXI[A1, A2, A3, A4, B1, B2, _, _]](this)
        TransferOpt.decompose(thiz.g2) match {
          case Right((i, j)) =>
            decompose(assocRL > par(g1.asShuffle, j) > that.g.asShuffle) match {
              case Decomposition(f1, f2, h) => Xfer(swap > par(i, f1), f2, AssocLR(h))
            }
          case Left(t) =>
            t.ixi_sndThis_xi(thiz.g1, that)
        }
      }

      override def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
        that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
      )(using
        ev1: (B1 |*| B2) =:= (B11 |*| B12),
        ev2: (B3 |*| B4) =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        BiTransferOpt(ev1.biSubst(g1), ev2.biSubst(g2)).ixi_this_ixi(that)

      override def assocLR_this_assocRL[X, Y1, Y2](h: AssocRL[X, (B1 |*| B2), (B3 |*| B4), Y1, Y2]): ((X |*| (A1 |*| A2)) |*| (A3 |*| A4)) ~⚬ ((Y1 |*| Y2) |*| (B3 |*| B4)) =
        decompose(assocLR > snd(g1.asShuffle) > h.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(assocRL > fst(f1), fst(f2), IXI(h, g2))

      override def assocLR_this_xi[X, Y2, Y3](h: XI[X, (B1 |*| B2), (B3 |*| B4), Y2, Y3]): ((X |*| (A1 |*| A2)) |*| (A3 |*| A4)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        decompose(assocLR > snd(g2.asShuffle) > h.g.asShuffle) match
          case Decomposition(f1, f2, h2) =>
            Xfer(xi > snd(f1), snd(f2), IXI(g1, h2))

      override def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, (B1 |*| B2), (B3 |*| B4), Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| (A1 |*| A2)) |*| (A3 |*| A4)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        decompose(assocLR > snd(g1.asShuffle) > that.g1.asShuffle) match
          case Decomposition(f1, f2, h1) =>
            decompose(assocLR > snd(g2.asShuffle) > that.g2.asShuffle) match
              case Decomposition(f3, f4, h2) =>
                Xfer(ixi > par(f1, f3), par(f2, f4), IXI(h1, h2))

      override def assocRL_this_assocLR[X, Y2, Y3](h: AssocLR[(B1 |*| B2), (B3 |*| B4), X, Y2, Y3]): ((A1 |*| A2) |*| ((A3 |*| A4) |*| X)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        decompose(assocRL[A2, A4, X] > fst(g2.asShuffle) > h.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(snd(f1), assocLR[A3, A4, X] > snd(f2), IXI(g1, h))

      override def assocRL_this_ix[X, Y1, Y2](that: IX[(B1 |*| B2), (B3 |*| B4), X, Y1, Y2]): ((A1 |*| A2) |*| ((A3 |*| A4) |*| X)) ~⚬ ((Y1 |*| Y2) |*| (B3 |*| B4)) =
        decompose(AssocRL(g1).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(fst(f1), ix > fst(f2), IXI(h, g2))
        }

      override def assocRL_this_ixi[X1, X2, Y1, Y2, Y3, Y4](h: IXI[(B1 |*| B2), (B3 |*| B4), X1, X2, Y1, Y2, Y3, Y4]): ((A1 |*| A2) |*| ((A3 |*| A4) |*| (X1 |*| X2))) ~⚬ ((Y1 |*| Y2) |*| (Y3 |*| Y4)) =
        decompose(assocRL > fst(g1.asShuffle) > h.g1.asShuffle) match
          case Decomposition(f1, f2, h1) =>
            decompose(assocRL > fst(g2.asShuffle) > h.g2.asShuffle) match
              case Decomposition(f3, f4, h2) =>
                Xfer(par(f1, f3), ixi > par(f2, f4), IXI(h1, h2))

      override def ix_this_assocLR[X, Y2, Y3](that: AssocLR[(B1 |*| B2), (B3 |*| B4), X, Y2, Y3]): (((A1 |*| A2) |*| X) |*| (A3 |*| A4)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        decompose(ix > fst(g2.asShuffle) > that.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(assocLR > snd(f1), snd(f2), IXI(g1, h))

      override def ix_this_ix[X, Y1, Y2](that: IX[(B1 |*| B2), (B3 |*| B4), X, Y1, Y2]): (((A1 |*| A2) |*| X) |*| (A3 |*| A4)) ~⚬ ((Y1 |*| Y2) |*| (B3 |*| B4)) =
        decompose(IX(g1).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(ix > fst(f1), fst(f2), IXI(h, g2))
        }

      override def ix_this_ixi[P1, P2, Q1, Q2, Q3, Q4](
        that: IXI[B1 |*| B2, B3 |*| B4, P1, P2, Q1, Q2, Q3, Q4],
      ): (((A1 |*| A2) |*| (P1 |*| P2)) |*| (A3 |*| A4)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        decompose(ix > fst(g1.asShuffle) > that.g1.asShuffle) match
          case Decomposition(f1, f2, h1) =>
            decompose(ix > fst(g2.asShuffle) > that.g2.asShuffle) match
              case Decomposition(f3, f4, h2) =>
                Xfer(ixi > par(f1, f3), par(f2, f4), IXI(h1, h2))

      override def xi_this_assocRL[X, Y1, Y2](g: AssocRL[X, (B1 |*| B2), (B3 |*| B4), Y1, Y2]): ((A1 |*| A2) |*| (X |*| (A3 |*| A4))) ~⚬ ((Y1 |*| Y2) |*| (B3 |*| B4)) =
        decompose(xi > snd(g1.asShuffle) > g.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(fst(f1), assocRL > fst(f2), IXI(h, g2))

      override def xi_this_xi[X, C2, C3](
        g: XI[X, (B1 |*| B2), (B3 |*| B4), C2, C3],
      ): ((A1 |*| A2) |*| (X |*| (A3 |*| A4))) ~⚬ ((B1 |*| B2) |*| (C2 |*| C3)) =
        decompose(xi > snd(g2.asShuffle) > g.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(snd(f1), xi > snd(f2), IXI(g1, h))

      override def xi_this_ixi[P1, P2, C1, C2, C3, C4](g: IXI[P1, P2, B1 |*| B2, B3 |*| B4, C1, C2, C3, C4]): (A1 |*| A2 |*| (P1 |*| P2 |*| (A3 |*| A4))) ~⚬ (C1 |*| C2 |*| (C3 |*| C4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_ixi")

      override def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
        g2: TransferOpt[P1, P2, Q1, Q2],
        that: AssocLR[(B1 |*| B2), (B3 |*| B4), Q1 |*| Q2, R2, R3],
      ): (((A1 |*| A2) |*| P1) |*| ((A3 |*| A4) |*| P2)) ~⚬ ((B1 |*| B2) |*| (R2 |*| R3)) =
        decompose(ixi > par(this.g2.asShuffle, g2.asShuffle) > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(assocLR > snd(f1), assocLR > snd(f2), IXI(this.g1, h))
        }

      override def ixi_sndThis_assocRL[P1, P2, Q1, Q2, R1, R2](
        g: TransferOpt[P1, P2, Q1, Q2],
        that: AssocRL[Q1 |*| Q2, (B1 |*| B2), (B3 |*| B4), R1, R2],
      ): ((P1 |*| (A1 |*| A2)) |*| (P2 |*| (A3 |*| A4))) ~⚬ ((R1 |*| R2) |*| (B3 |*| B4)) =
        decompose(ixi > par(g.asShuffle, g1.asShuffle) > that.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(assocRL > fst(f1), assocRL > fst(f2), IXI(h, g2))

      override def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
        g: TransferOpt[P1, P2, Q1, Q2],
        that: XI[Q1 |*| Q2, (B1 |*| B2), (B3 |*| B4), R2, R3],
      ): ((P1 |*| (A1 |*| A2)) |*| (P2 |*| (A3 |*| A4))) ~⚬ ((B1 |*| B2) |*| (R2 |*| R3)) =
        decompose(ixi > par(g.asShuffle, g2.asShuffle) > that.g.asShuffle) match
          case Decomposition(f1, f2, h) =>
            Xfer(xi > snd(f1), xi > snd(f2), IXI(g1, h))

      override def invert: Xfer[(B1 |*| B2), (B3 |*| B4), ?, ?, A1 |*| A2, A3 |*| A4] =
        Xfer(g1.asShuffle.invert, g2.asShuffle.invert, IXI(TransferOpt.None(), TransferOpt.None()))

      override def ixiPairWith_:[X1, X2, X3, X4, Y1, Y2, Y3, Y4](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2, Y3, Y4],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1 |*| A2, A3 |*| A4, Y1 |*| Y2, Y3 |*| Y4, (B1 |*| B2), (B3 |*| B4)] =
        BiTransferOpt.IXI_IXI(that, this)

      override def nonePairWith_:[X1, X2](
        that: TransferOpt.None[X1, X2],
      ): BiTransferOpt[X1, X2, A1 |*| A2, A3 |*| A4, X1, X2, (B1 |*| B2), (B3 |*| B4)] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3 |*| A4, X2, X1, (B1 |*| B2), (B3 |*| B4)] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def pairWith[X3, X4, Z1, Z2](that: TransferOpt[X3, X4, Z1, Z2]): BiTransferOpt[A1 |*| A2, A3 |*| A4, X3, X4, (B1 |*| B2), (B3 |*| B4), Z1, Z2] =
        this ixiPairWith_: that
    }
  }

  sealed trait BiTransferOpt[A1, A2, A3, A4, B1, B2, B3, B4] {
    import Transfer.IXI

    def ixi_this_ixi[C1, C2, C3, C4](
      that: IXI[B1, B2, B3, B4, C1, C2, C3, C4],
    ): ((A1 |*| A3) |*| (A2 |*| A4)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4))
  }

  object BiTransferOpt {
    import Transfer.{AssocLR, AssocRL, IX, IXI, Swap, XI}

    case class None_None[A1, A2, A3, A4]() extends BiTransferOpt[A1, A2, A3, A4, A1, A2, A3, A4] {
      override def ixi_this_ixi[C1, C2, C3, C4](
        that: IXI[A1, A2, A3, A4, C1, C2, C3, C4],
      ): ((A1 |*| A3) |*| (A2 |*| A4)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        par(that.g1.asShuffle, that.g2.asShuffle)
    }

    case class None_AssocLR[A1, A2, A3, A4, A5, B3, B4](
      t2: AssocLR[A3, A4, A5, B3, B4],
    ) extends BiTransferOpt[A1, A2, A3 |*| A4, A5, A1, A2, A3, B3 |*| B4] {
      override def ixi_this_ixi[C1, C2, C3, C4](
        that: IXI[A1, A2, A3, B3 |*| B4, C1, C2, C3, C4],
      ): ((A1 |*| (A3 |*| A4)) |*| (A2 |*| A5)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        decompose(XI(t2.g).asShuffle > that.g2.asShuffle) match
          case Decomposition(f1, f2, h2) =>
            Xfer(assocRL > par(that.g1.asShuffle, f1), f2, AssocLR(h2))
    }

    case class None_IX[A1, A2, A3, A4, A5, B3, B4](
      ix: IX[A3, A4, A5, B3, B4],
    ) extends BiTransferOpt[A1, A2, A3 |*| A4, A5, A1, A2, B3 |*| B4, A4] {

      override def ixi_this_ixi[C1, C2, C3, C4](
        that: IXI[A1, A2, B3 |*| B4, A4, C1, C2, C3, C4],
      ): ((A1 |*| (A3 |*| A4)) |*| (A2 |*| A5)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        decompose(AssocLR(ix.g).asShuffle > that.g1.asShuffle) match {
          case Decomposition(f1, f2, h1) =>
            decompose(swap > that.g2.asShuffle) match {
              case Decomposition(f3, f4, h2) =>
                Xfer(assocRL > par(f1, f3), swap > par(f2, f4), IXI(h1, h2))
            }
        }

    }

    case class Swap_AssocRL[A1, A2, A3, A4, A5, B3, B4](
      swp: Swap[A1, A2],
      arl: AssocRL[A3, A4, A5, B3, B4],
    ) extends BiTransferOpt[A1, A2, A3, A4 |*| A5, A2, A1, B3 |*| B4, A5] {

      override def ixi_this_ixi[C1, C2, C3, C4](
        that: IXI[A2, A1, B3 |*| B4, A5, C1, C2, C3, C4],
      ): ((A1 |*| A3) |*| (A2 |*| (A4 |*| A5))) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_this_ixi")
    }

    case class IXI_IXI[A1, A2, A3, A4, A5, A6, A7, A8, B1, B2, B3, B4, B5, B6, B7, B8](
      ixi1: IXI[A1, A2, A3, A4, B1, B2, B3, B4],
      ixi2: IXI[A5, A6, A7, A8, B5, B6, B7, B8],
    ) extends BiTransferOpt[A1 |*| A2, A3 |*| A4, A5 |*| A6, A7 |*| A8, B1 |*| B2, B3 |*| B4, B5 |*| B6, B7 |*| B8] {

      override def ixi_this_ixi[C1, C2, C3, C4](
        that: IXI[B1 |*| B2, B3 |*| B4, B5 |*| B6, B7 |*| B8, C1, C2, C3, C4],
      ): (((A1 |*| A2) |*| (A5 |*| A6)) |*| ((A3 |*| A4) |*| (A7 |*| A8))) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        par(ixi, ixi) > ixi > par(
          ixi > par(ixi1.g1.asShuffle, ixi2.g1.asShuffle) > that.g1.asShuffle,
          ixi > par(ixi1.g2.asShuffle, ixi2.g2.asShuffle) > that.g2.asShuffle,
        )
    }

    def apply[A1, A2, A3, A4, B1, B2, B3, B4](
      t1: TransferOpt[A1, A2, B1, B2],
      t2: TransferOpt[A3, A4, B3, B4],
    ): BiTransferOpt[A1, A2, A3, A4, B1, B2, B3, B4] =
      t1 pairWith t2
  }

  extension [A, B](ev: A =:= B) {
    def zip[C, D](that: C =:= D): (A |*| C) =:= (B |*| D) =
      that.substituteCo[[x] =>> (A |*| C) =:= (B |*| x)](
        ev.substituteCo[[x] =>> (A |*| C) =:= (x |*| C)](
          summon[(A |*| C) =:= (A |*| C)]
        )
      )
  }
}