package libretto.lambda

import libretto.util.BiInjective
import libretto.util.BiInjective._

class Shuffle[|*|[_, _]](using inj: BiInjective[|*|]) {
  sealed trait ~⚬[A, B] {
    import ~⚬._

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
                case id: Id0[_, _] => id.ev.substituteCo(par(f1 > g1, f2 > g2))
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

    def chaseFw[F[_], X](i: Focus[|*|, F])(using ev: A =:= F[X]): ChaseFwRes[F, X, B]
    def chaseBw[G[_], X](i: Focus[|*|, G])(using ev: B =:= G[X]): ChaseBwRes[A, G, X]

    def to[C](using ev: B =:= C): A ~⚬ C =
      ev.substituteCo(this)
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

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: X =:= F[T]): ChaseFwRes[F, T, X] =
        ChaseFwRes.Transported[F, T, F, X]([t] => (_: Unit) => Id[F[t]](), i, ev.flip)

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: X =:= G[T]): ChaseBwRes[X, G, T] =
        ChaseBwRes.Transported[X, G, G, T](ev, i, [t] => (_: Unit) => Id[G[t]]())
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
    }

    /** An operator that transfers resources across inputs. */
    case class Xfer[A1, A2, X1, X2, B1, B2](f1: A1 ~⚬ X1, f2: A2 ~⚬ X2, transfer: Transfer[X1, X2, B1, B2]) extends Composed[A1 |*| A2, B1 |*| B2] {
      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: (A1 |*| A2) =:= F[T]): ChaseFwRes[F, T, B1 |*| B2] =
        i match
          case Focus.Id() =>
            ChaseFwRes.Split(summon[T =:= F[T]] andThen ev.flip)
          case i: Focus.Fst[pair, f1, a2] =>
            val inj(a1f1t, a2a2) = ev andThen summon[F[T] =:= (f1[T] |*| a2)]
            f1.chaseFw[f1, T](i.i)(using a1f1t) match
              case ChaseFwRes.Split(ev) =>
                ChaseFwRes.Split(ev)
              case tr: ChaseFwRes.Transported[f1, t, g1, x1] =>
                transfer.chaseFw[[t] =>> g1[t] |*| X2, T](tr.g.inFst[X2])(using tr.ev zip summon[X2 =:= X2]) match
                  case ChaseFwRes.Split(ev) =>
                    ChaseFwRes.Split(ev)
                  case tr1: ChaseFwRes.Transported[g, t, h, b] =>
                    ChaseFwRes.Transported[F, T, h, B1 |*| B2](
                      [t] => (_: Unit) => snd(Id0(a2a2.flip)) > par(tr.s[t](()), f2) > tr1.s[t](()),
                      tr1.g,
                      tr1.ev,
                    )
          case Focus.Snd(i2) =>
            ???

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[T]): ChaseBwRes[A1 |*| A2, G, T] =
        transfer.chaseBw(i) after par(f1, f2)
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
    ): Either[Xfer[X1, X2, _, _, Y1, Y2], (X1 ~⚬ Y1, X2 ~⚬ Y2)] =
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

    def decompose[X1, X2, Z1, Z2](f: (X1 |*| X2) ~⚬ (Z1 |*| Z2)): Decomposition[X1, X2, _, _, Z1, Z2] =
      f match {
        case i: Id0[X1 |*| X2, Z1 |*| Z2] => Decomposition(Id(), Id(), TransferOpt.None0(i.ev))
        case Bimap(Par(f1, f2))           => Decomposition(f1, f2, TransferOpt.None())
        case Xfer(f1, f2, xfer)           => Decomposition(f1, f2, xfer)
      }

    def decompose1[X1, X2, Z](f: (X1 |*| X2) ~⚬ Z): Decomposition1[X1, X2, _, _, _, _, Z] =
      f match {
        case Id()               => Decomposition1(Id(), Id(), TransferOpt.None(), implicitly)
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

    sealed trait ChaseFwRes[F[_], X, B]

    object ChaseFwRes {
      case class Transported[F[_], X, G[_], B](
        s: [t] => Unit => F[t] ~⚬ G[t],
        g: Focus[|*|, G],
        ev: G[X] =:= B,
      ) extends ChaseFwRes[F, X, B]

      case class Split[F[_], X, X1, X2, B](ev: X =:= (X1 |*| X2)) extends ChaseFwRes[F, X, B]
    }

    sealed trait ChaseBwRes[A, G[_], X] {
      def after[Z](f: Z ~⚬ A): ChaseBwRes[Z, G, X]
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
      }

      case class Split[A, G[_], X, X1, X2](ev: X =:= (X1 |*| X2)) extends ChaseBwRes[A, G, X] {
        override def after[Z](f: Z ~⚬ A): ChaseBwRes[Z, G, X] =
          Split(ev)
      }
    }
  }
  import ~⚬._

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

    def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: (X1 |*| X2) =:= F[T]): ChaseFwRes[F, T, Y1 |*| Y2] =
      ???

    def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (Y1 |*| Y2) =:= G[T]): ChaseBwRes[X1 |*| X2, G, T] =
      ???
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
        case x: Transfer[_, _, _, _] => Xfer(Id(), Id(), x)
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
    import Transfer._

    def after[Z1, Z2](that: Transfer[Z1, Z2, A1, A2]): (Z1 |*| Z2) ~⚬ (B1 |*| B2)

    def thenBi[C1, C2](g1: B1 ~⚬ C1, g2: B2 ~⚬ C2): Xfer[A1, A2, _, _, C1, C2]

    def thenSwap: (A1 |*| A2) ~⚬ (B2 |*| B1)

    def thenAssocLR[B11, B12, C2, C3](
      that: AssocLR[B11, B12, B2, C2, C3],
    )(implicit
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
    )(implicit
      ev: B2 =:= (B21 |*| B22),
    ): (A1 |*| A2) ~⚬ (B21 |*| (C2 |*| C3))

    def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
      that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
    )(implicit
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

    def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
      g2: TransferOpt[P1, P2, Q1, Q2],
      that: AssocLR[B1, B2, Q1 |*| Q2, R2, R3],
    ): ((A1 |*| P1) |*| (A2 |*| P2)) ~⚬ (B1 |*| (R2 |*| R3))

    def ixi_sndThis_assocRL[P1, P2, Q1, Q2, R1, R2](
      g1: TransferOpt[P1, P2, Q1, Q2],
      that: AssocRL[Q1 |*| Q2, B1, B2, R1, R2],
    ): ((P1 |*| A1) |*| (P2 |*| A2)) ~⚬ ((R1 |*| R2) |*| B2)

    def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
      g1: TransferOpt[P1, P2, Q1, Q2],
      that: XI[Q1 |*| Q2, B1, B2, R2, R3],
    ): ((P1 |*| A1) |*| (P2 |*| A2)) ~⚬ (B1 |*| (R2 |*| R3))

    def invert: Xfer[B1, B2, _, _, A1, A2]

    def >[C1, C2](that: Transfer[B1, B2, C1, C2]): (A1 |*| A2) ~⚬ (C1 |*| C2) =
      that after this

    def to[C1, C2](implicit ev: (B1 |*| B2) =:= (C1 |*| C2)): Transfer[A1, A2, C1, C2] = {
      val (ev1, ev2) = inj.unapply(ev)
      ev1.substituteCo[Transfer[A1, A2, *, C2]](ev2.substituteCo(this))
    }

    override def fold[->[_, _]](using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> (B1 |*| B2) = {
      import ev._

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

    def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A1 |*| A2)): ChaseFwRes[F, T, B1 |*| B2]
    def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2) =:= G[T]): ChaseBwRes[A1 |*| A2, G, T]
  }

  object Transfer {
    case class Swap[X1, X2]() extends Transfer[X1, X2, X2, X1] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, X1, X2]): (Z1 |*| Z2) ~⚬ (X2 |*| X1) =
        that.thenSwap

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (X1 |*| X2)): ChaseFwRes[F, T, X2 |*| X1] =
        i match
          case Focus.Id() =>
            ChaseFwRes.Split(summon[T =:= F[T]] andThen ev)
          case fst: Focus.Fst[p, f1, b] =>
            val inj(f1tx1, bx2) = summon[(f1[T] |*| b) =:= (X1 |*| X2)]
            ChaseFwRes.Transported[[t] =>> f1[t] |*| b, T, [t] =>> b |*| f1[t], X2 |*| X1]([t] => (_: Unit) => swap[f1[t], b], fst.i.inSnd, bx2 zip f1tx1)
          case snd: Focus.Snd[p, f2, b] =>
            UnhandledCase.raise(s"Swap.chaseFw($snd)")

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (X2 |*| X1) =:= G[T]): ChaseBwRes[X1 |*| X2, G, T] =
        i match
          case Focus.Id() =>
            ChaseBwRes.Split((ev andThen summon[G[T] =:= T]).flip)
          case fst: Focus.Fst[p, f, b] =>
            val inj(x2ft, x1b) = ev andThen summon[G[T] =:= (f[T] |*| b)]
            ChaseBwRes.Transported[X1 |*| X2, [t] =>> b |*| f[t], [t] =>> f[t] |*| b, T](x1b zip x2ft, fst.i.inSnd, [t] => (_: Unit) => swap[b, f[t]])
          case snd: Focus.Snd[p, f, a] =>
            val inj(x2b, x1ft) = ev andThen summon[G[T] =:= (a |*| f[T])]
            ChaseBwRes.Transported[X1 |*| X2, [t] =>> f[t] |*| a, [t] =>> a |*| f[t], T](x1ft zip x2b, snd.i.inFst, [t] => (_: Unit) => swap[f[t], a])

      override def thenBi[C1, C2](g1: X2 ~⚬ C1, g2: X1 ~⚬ C2): Xfer[X1, X2, _, _, C1, C2] =
        Xfer(g2, g1, Swap())

      override def thenSwap: (X1 |*| X2) ~⚬ (X1 |*| X2) =
        Id()

      override def thenAssocLR[X21, X22, C2, C3](
        that: AssocLR[X21, X22, X1, C2, C3],
      )(implicit
        ev: X2 =:= (X21 |*| X22),
      ): (X1 |*| X2) ~⚬ (X21 |*| (C2 |*| C3)) = {
        val res = swap_then_assocLR(ev.substituteCo(this), that)
        ev.substituteContra[[x] =>> (X1 |*| x) ~⚬ (X21 |*| (C2 |*| C3))](res)
      }

      override def thenAssocRL[B21, B22, C1, C2](
        that: AssocRL[X2, B21, B22, C1, C2],
      )(using
        ev: X1 =:= (B21 |*| B22),
      ): (X1 |*| X2) ~⚬ ((C1 |*| C2) |*| B22) = {
        val res = swap_then_assocRL(ev.substituteCo[[x] =>> Swap[x, X2]](this), that)
        ev.substituteContra[[x] =>> (x |*| X2) ~⚬ ((C1 |*| C2) |*| B22)](res)
      }

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
      )(implicit
        ev: X1 =:= (X11 |*| X12),
      ): (X1 |*| X2) ~⚬ (X11 |*| (C2 |*| C3)) =
        decompose(swap > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(Id0(ev) > snd(f1), f2, AssocLR(h))
        }

      override def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
        that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
      )(implicit
        ev1: X2 =:= (B11 |*| B12),
        ev2: X1 =:= (B21 |*| B22),
      ): (X1 |*| X2) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenIXI($that)")

      override def assocLR_this_assocRL[X, Y1, Y2](h: AssocRL[X, X2, X1, Y1, Y2]): ((X |*| X1) |*| X2) ~⚬ ((Y1 |*| Y2) |*| X1) =
        IX[X, X1, X2, Y1, Y2](h.g).asShuffle

      override def assocLR_this_xi[X, Y2, Y3](h: XI[X, X2, X1, Y2, Y3]): ((X |*| X1) |*| X2) ~⚬ (X2 |*| (Y2 |*| Y3)) =
        Xfer(h.g.asShuffle, id, Swap())

      override def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, X2, X1, Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| X1) |*| X2) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_ixi")

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
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_ixi")

      override def xi_this_assocRL[X, Y1, Y2](g: AssocRL[X, X2, X1, Y1, Y2]): (X1 |*| (X |*| X2)) ~⚬ ((Y1 |*| Y2) |*| X1) =
        Xfer(Id(), g.g.asShuffle, Swap())

      override def xi_this_xi[X, C2, C3](g: XI[X, X2, X1, C2, C3]): (X1 |*| (X |*| X2)) ~⚬ (X2 |*| (C2 |*| C3)) =
        decompose(swap > g.g.asShuffle) match {
          case Decomposition(h1, h2, h) => Xfer(h1, fst(h2) > swap, XI(h))
        }

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

      override def invert: Xfer[X2, X1, _, _, X1, X2] =
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

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A1 |*| A2 |*| A3)): ChaseFwRes[F, T, A1 |*| (B2 |*| B3)] =
        UnhandledCase.raise(s"AssocLR.chaseFw($i)")

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (A1 |*| (B2 |*| B3)) =:= G[T]): ChaseBwRes[A1 |*| A2 |*| A3, G, T] = ???

      override def thenBi[C1, C2](g1: A1 ~⚬ C1, g2: (B2 |*| B3) ~⚬ C2): Xfer[A1 |*| A2, A3, _, _, C1, C2] =
        decompose1(g.asShuffle > g2) match {
          case Decomposition1(f1, f2, g, ev) => ev.substituteCo(Xfer(par(g1, f1), f2, AssocLR(g)))
        }

      override def thenSwap: ((A1 |*| A2) |*| A3) ~⚬ ((B2 |*| B3) |*| A1) =
        Xfer(swap, id, IX(g))

      override def thenAssocLR[A11, A12, C2, C3](
        that: AssocLR[A11, A12, B2 |*| B3, C2, C3],
      )(implicit
        ev: A1 =:= (A11 |*| A12),
      ): ((A1 |*| A2) |*| A3) ~⚬ (A11 |*| (C2 |*| C3)) = {
        val res = assocLR_then_assocLR(ev.substituteCo[AssocLR[*, A2, A3, B2, B3]](this), that)
        ev.substituteContra[[x] =>> ((x |*| A2) |*| A3) ~⚬ (A11 |*| (C2 |*| C3))](res)
      }

      override def thenAssocRL[B21, B22, C1, C2](
        that: AssocRL[A1, B21, B22, C1, C2],
      )(using
        ev: (B2 |*| B3) =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ ((C1 |*| C2) |*| B22) =
        assocLR_then_assocRL(ev.biSubst[AssocLR[A1, A2, A3, *, *]](this), that)

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
      )(implicit
        ev: (B2 |*| B3) =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (B21 |*| (C2 |*| C3)) =
        assocLR_then_xi(ev.biSubst[AssocLR[A1, A2, A3, *, *]](this), that)

      override def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
        that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
      )(implicit
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
        UnhandledCase.raise(s"$h")

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

      override def xi_this_xi[X, C2, C3](g: XI[X, A1, B2 |*| B3, C2, C3]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ (A1 |*| (C2 |*| C3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_xi($g)")

      override def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
        g2: TransferOpt[P1, P2, Q1, Q2],
        that: AssocLR[A1, B2 |*| B3, Q1 |*| Q2, R2, R3],
      ): (((A1 |*| A2) |*| P1) |*| (A3 |*| P2)) ~⚬ (A1 |*| (R2 |*| R3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_fstThis_assocLR")

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

      override def invert: Xfer[A1, B2 |*| B3, _, _, A1 |*| A2, A3] =
        Xfer(id, g.asShuffle.invert, AssocRL(TransferOpt.None()))

      override def ixiPairWith_:[X1, X2, X3, X4, Y1, Y2, Y3, Y4](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2, Y3, Y4],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1 |*| A2, A3, Y1 |*| Y2, Y3 |*| Y4, A1, B2 |*| B3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")

      override def nonePairWith_:[X1, X2](that: TransferOpt.None[X1, X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3, X1, X2, A1, B2 |*| B3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3, X2, X1, A1, B2 |*| B3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def pairWith[X3, X4, Z1, Z2](that: TransferOpt[X3, X4, Z1, Z2]): BiTransferOpt[A1 |*| A2, A3, X3, X4, A1, B2 |*| B3, Z1, Z2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.pairWith($that)")
    }

    case class AssocRL[A1, A2, A3, B1, B2](g: TransferOpt[A1, A2, B1, B2]) extends Transfer[A1, A2 |*| A3, B1 |*| B2, A3] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1, A2 |*| A3]): (Z1 |*| Z2) ~⚬ ((B1 |*| B2) |*| A3) =
        that.thenAssocRL(this)

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A1 |*| (A2 |*| A3))): ChaseFwRes[F, T, B1 |*| B2 |*| A3] =
        UnhandledCase.raise(s"AssocRL.chaseFw($i)")

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2 |*| A3) =:= G[T]): ChaseBwRes[A1 |*| (A2 |*| A3), G, T] = ???

      override def thenBi[C1, C2](g1: (B1 |*| B2) ~⚬ C1, g2: A3 ~⚬ C2): Xfer[A1, A2 |*| A3, _, _, C1, C2] =
        decompose1(g.asShuffle > g1) match {
          case Decomposition1(f1, f2, h, ev) => ev.substituteCo[Xfer[A1, A2 |*| A3, _, _, *, C2]](Xfer(f1, par(f2, g2), AssocRL(h)))
        }

      override def thenSwap: (A1 |*| (A2 |*| A3)) ~⚬ (A3 |*| (B1 |*| B2)) =
        decompose(g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, fst(f2) > swap, XI(h))
        }

      override def thenAssocLR[D1, D2, C2, C3](
        that: AssocLR[D1, D2, A3, C2, C3],
      )(implicit
        ev: (B1 |*| B2) =:= (D1 |*| D2),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (D1 |*| (C2 |*| C3)) =
        assocRL_then_assocLR(ev.biSubst[AssocRL[A1, A2, A3, *, *]](this), that)

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
      )(implicit
        ev: A3 =:= (A31 |*| A32),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (A31 |*| (C2 |*| C3)) =
        decompose(assocRL > fst(g.asShuffle) > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) =>
            Xfer(f1, snd(id[A3].to[A31 |*| A32]) > xi > snd(f2), XI(h))
        }

      override def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
        that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
      )(implicit
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
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_assocRL($h)")

      override def assocLR_this_xi[X, Y2, Y3](h: XI[X, B1 |*| B2, A3, Y2, Y3]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        Xfer(swap, id, IXI(g, h.g))

      override def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, B1 |*| B2, A3, Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| A1) |*| (A2 |*| A3)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_ixi")

      override def assocRL_this_assocLR[X, Y2, Y3](h: AssocLR[B1 |*| B2, A3, X, Y2, Y3]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        Xfer(id, AssocLR(h.g).asShuffle, AssocRL(g))

      override def assocRL_this_ix[X, Y1, Y2](that: IX[B1 |*| B2, A3, X, Y1, Y2]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ ((Y1 |*| Y2) |*| A3) =
        decompose(AssocRL(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, ix > fst(f2), AssocRL(h))
        }

      override def assocRL_this_ixi[X1, X2, Y1, Y2, Y3, Y4](h: IXI[B1 |*| B2, A3, X1, X2, Y1, Y2, Y3, Y4]): (A1 |*| ((A2 |*| A3) |*| (X1 |*| X2))) ~⚬ ((Y1 |*| Y2) |*| (Y3 |*| Y4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ixi")

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
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_ixi")

      override def xi_this_xi[X, C2, C3](h: XI[X, B1 |*| B2, A3, C2, C3]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ ((B1 |*| B2) |*| (C2 |*| C3)) =
        Xfer(Id(), XI(h.g).asShuffle, AssocRL(g))

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
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_sndThis_assocRL")

      override def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: XI[Q1 |*| Q2, B1 |*| B2, A3, R2, R3],
      ): ((P1 |*| A1) |*| (P2 |*| (A2 |*| A3))) ~⚬ ((B1 |*| B2) |*| (R2 |*| R3)) =
        decompose(assocRL > fst(g1.asShuffle) > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(swap > snd(f1), xi > snd(f2), IXI(g, h))
        }

      override def invert: Xfer[B1 |*| B2, A3, _, _, A1, A2 |*| A3] =
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

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A1 |*| A2 |*| A3)): ChaseFwRes[F, T, B1 |*| B2 |*| A2] =
        UnhandledCase.raise(s"IX.chaseFw($i)")

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2 |*| A2) =:= G[T]): ChaseBwRes[A1 |*| A2 |*| A3, G, T] = ???

      override def thenBi[C1, C2](g1: (B1 |*| B2) ~⚬ C1, g2: A2 ~⚬ C2): Xfer[A1 |*| A2, A3, _, _, C1, C2] =
        decompose1(g.asShuffle > g1) match {
          case Decomposition1(f1, f2, h, ev) => ev.substituteCo[Xfer[A1 |*| A2, A3, _, _, *, C2]](Xfer(par(f1, g2), f2, IX(h)))
        }

      override def thenSwap: ((A1 |*| A2) |*| A3) ~⚬ (A2 |*| (B1 |*| B2)) =
        Xfer(swap, id, AssocLR(g))

      override def thenAssocLR[D1, D2, C2, C3](
        that: AssocLR[D1, D2, A2, C2, C3],
      )(implicit
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
      ): ((A1 |*| A2) |*| A3) ~⚬ ((C1 |*| C2) |*| X2) = {
        val res = ix_then_assocRL(ev.substituteCo[IX[A1, *, A3, B1, B2]](this), that)
        ev.substituteContra[[x] =>> ((A1 |*| x) |*| A3) ~⚬ ((C1 |*| C2) |*| X2)](res)
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
      )(implicit
        ev: A2 =:= (A21 |*| A22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (A21 |*| (C2 |*| C3)) =
        decompose(IX(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(snd(Id0(ev)) > xi > snd(f1), f2, AssocLR(h))
        }

      override def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
        that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
      )(implicit
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
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ixi")

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
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_xi($h)")

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
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_sndThis_assocRL")

      override def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: XI[Q1 |*| Q2, (B1 |*| B2), A2, R2, R3],
      ): ((P1 |*| (A1 |*| A2)) |*| (P2 |*| A3)) ~⚬ ((B1 |*| B2) |*| (R2 |*| R3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_sndThis_xi")

      override def invert: Xfer[(B1 |*| B2), A2, _, _, A1 |*| A2, A3] =
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

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A1 |*| (A2 |*| A3))): ChaseFwRes[F, T, A2 |*| (B2 |*| B3)] =
        UnhandledCase.raise(s"XI.chaseFw($i)")

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (A2 |*| (B2 |*| B3)) =:= G[T]): ChaseBwRes[A1 |*| (A2 |*| A3), G, T] = ???

      override def thenBi[C1, C2](g1: A2 ~⚬ C1, g2: (B2 |*| B3) ~⚬ C2): Xfer[A1, A2 |*| A3, _, _, C1, C2] =
        decompose1(g.asShuffle > g2) match {
          case Decomposition1(f1, f2, h, ev) => ev.substituteCo(Xfer(f1, par(g1, f2), XI(h)))
        }

      override def thenSwap: (A1 |*| (A2 |*| A3)) ~⚬ ((B2 |*| B3) |*| A2) =
        Xfer(Id(), swap, AssocRL(g))

      override def thenAssocLR[A21, A22, C2, C3](
        that: AssocLR[A21, A22, B2 |*| B3, C2, C3],
      )(implicit
        ev: A2 =:= (A21 |*| A22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (A21 |*| (C2 |*| C3)) = {
        val res = xi_then_assocLR(ev.substituteCo[[x] =>> XI[A1, x, A3, B2, B3]](this), that)
        ev.substituteContra[[x] =>> (A1 |*| (x |*| A3)) ~⚬ (A21 |*| (C2 |*| C3))](res)
      }

      override def thenAssocRL[B21, B22, C1, C2](
        that: AssocRL[A2, B21, B22, C1, C2],
      )(using
        ev: (B2 |*| B3) =:= (B21 |*| B22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ ((C1 |*| C2) |*| B22) =
        xi_then_assocRL(ev.biSubst[XI[A1, A2, A3, *, *]](this), that)

      override def thenIX[B11, B12, C1, C2](
        that: IX[B11, B12, B2 |*| B3, C1, C2],
      )(using
        ev: A2 =:= (B11 |*| B12),
      ): (A1 |*| (A2 |*| A3)) ~⚬ ((C1 |*| C2) |*| B12) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenIX($that)")

      override def thenXI[B21, B22, C2, C3](
        that: XI[A2, B21, B22, C2, C3],
      )(implicit
        ev: (B2 |*| B3) =:= (B21 |*| B22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (B21 |*| (C2 |*| C3)) =
        xi_then_xi(ev.biSubst[XI[A1, A2, A3, *, *]](this), that)

      override def thenIXI[B11, B12, B21, B22, C1, C2, C3, C4](
        that: IXI[B11, B12, B21, B22, C1, C2, C3, C4]
      )(implicit
        ev1: A2 =:= (B11 |*| B12),
        ev2: (B2 |*| B3) =:= (B21 |*| B22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        snd(fst(Id0(ev1))) > (TransferOpt.decompose(ev2.biSubst(g)) match {
          case Right((i, j)) =>
            decompose(swap > that.g1.asShuffle) match {
              case Decomposition(f1, f2, h) => Xfer(i > f1, Xfer(fst(f2), j, AssocLR(that.g2)), AssocRL(h))
            }
          case Left(t) =>
            UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenIXI($that)")
        })

      override def assocLR_this_assocRL[X, Y1, Y2](h: AssocRL[X, A2, B2 |*| B3, Y1, Y2]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        IXI(h.g, g).asShuffle

      override def assocLR_this_xi[X, Y2, Y3](h: XI[X, A2, B2 |*| B3, Y2, Y3]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ (A2 |*| (Y2 |*| Y3)) =
        UnhandledCase.raise(s"$h")

      override def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, A2, B2 |*| B3, Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| A1) |*| (A2 |*| A3)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_ixi")

      override def assocRL_this_assocLR[X, Y2, Y3](h: AssocLR[A2, B2 |*| B3, X, Y2, Y3]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ (A2 |*| (Y2 |*| Y3)) =
        decompose(assocRL > fst(g.asShuffle) > h.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, assocLR > snd(f2), XI(h))
        }

      override def assocRL_this_ix[X, Y1, Y2](h: IX[A2, B2 |*| B3, X, Y1, Y2]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        Xfer(id, IX(h.g).asShuffle, XI(g))

      override def assocRL_this_ixi[X1, X2, Y1, Y2, Y3, Y4](h: IXI[A2, B2 |*| B3, X1, X2, Y1, Y2, Y3, Y4]): (A1 |*| ((A2 |*| A3) |*| (X1 |*| X2))) ~⚬ ((Y1 |*| Y2) |*| (Y3 |*| Y4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ixi")

      override def ix_this_assocLR[X, Y2, Y3](that: AssocLR[A2, B2 |*| B3, X, Y2, Y3]): ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ (A2 |*| (Y2 |*| Y3)) =
        decompose(IX(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, snd(f2), XI(h))
        }

      override def ix_this_ix[X, Y1, Y2](that: IX[A2, B2 |*| B3, X, Y1, Y2]): ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        decompose(swap > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(swap > fst(f1), fst(f2), IXI(h, g))
        }

      override def ix_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[A2, B2 |*| B3, P1, P2, Q1, Q2, Q3, Q4]): ((A1 |*| (P1 |*| P2)) |*| (A2 |*| A3)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_ixi")

      override def xi_this_assocRL[X, Y1, Y2](h: AssocRL[X, A2, B2 |*| B3, Y1, Y2]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ ((Y1 |*| Y2) |*| (B2 |*| B3)) =
        Xfer(Id(), AssocRL(h.g).asShuffle, XI(g))

      override def xi_this_xi[X, C2, C3](g: XI[X, A2, B2 |*| B3, C2, C3]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ (A2 |*| (C2 |*| C3)) =
        decompose(xi(this.g.asShuffle) > g.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, xi > snd(f2), XI(h))
        }

      override def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
        g2: TransferOpt[P1, P2, Q1, Q2],
        that: AssocLR[A2, B2 |*| B3, Q1 |*| Q2, R2, R3],
      ): ((A1 |*| P1) |*| ((A2 |*| A3) |*| P2)) ~⚬ (A2 |*| (R2 |*| R3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_fstThis_assocLR")

      override def ixi_sndThis_assocRL[P1, P2, Q1, Q2, R1, R2](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: AssocRL[Q1 |*| Q2, A2, B2 |*| B3, R1, R2],
      ): ((P1 |*| A1) |*| (P2 |*| (A2 |*| A3))) ~⚬ ((R1 |*| R2) |*| (B2 |*| B3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_sndThis_assocRL")

      override def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: XI[Q1 |*| Q2, A2, B2 |*| B3, R2, R3],
      ): ((P1 |*| A1) |*| (P2 |*| (A2 |*| A3))) ~⚬ (A2 |*| (R2 |*| R3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_sndThis_xi")

      override def invert: Xfer[A2, B2 |*| B3, _, _, A1, A2 |*| A3] =
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

      override def chaseFw[F[_], T](i: Focus[|*|, F])(using ev: F[T] =:= (A1 |*| A2 |*| (A3 |*| A4))): ChaseFwRes[F, T, B1 |*| B2 |*| (B3 |*| B4)] =
        UnhandledCase.raise(s"IXI.chaseFw($i)")

      override def chaseBw[G[_], T](i: Focus[|*|, G])(using ev: (B1 |*| B2 |*| (B3 |*| B4)) =:= G[T]): ChaseBwRes[A1 |*| A2 |*| (A3 |*| A4), G, T] = ???

      override def thenBi[C1, C2](h1: (B1 |*| B2) ~⚬ C1, h2: (B3 |*| B4) ~⚬ C2): Xfer[A1 |*| A2, A3 |*| A4, _, _, C1, C2] =
        (decompose1(g1.asShuffle > h1), decompose1(g2.asShuffle > h2)) match {
          case (Decomposition1(g11, g12, h1, ev1), Decomposition1(g21, g22, h2, ev2)) =>
            (ev1 zip ev2).biSubst[Xfer[A1 |*| A2, A3 |*| A4, _, _, *, *]](Xfer(par(g11, g21), par(g12, g22), IXI(h1, h2)))
        }

      override def thenSwap: ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ ((B3 |*| B4) |*| (B1 |*| B2)) =
        Xfer(swap, swap, IXI(g2, g1))

      override def thenAssocLR[D1, D2, C2, C3](
        that: AssocLR[D1, D2, B3 |*| B4, C2, C3],
      )(implicit
        ev: (B1 |*| B2) =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (D1 |*| (C2 |*| C3)) = {
        val thiz = ev.biSubst[IXI[A1, A2, A3, A4, *, *, B3, B4]](this)
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

      override def thenIX[B11, B12, C1, C2](
        that: IX[B11, B12, B3 |*| B4, C1, C2],
      )(using
        ev: (B1 |*| B2) =:= (B11 |*| B12),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ ((C1 |*| C2) |*| B12) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenIX($that)")

      override def thenXI[D1, D2, C2, C3](
        that: XI[(B1 |*| B2), D1, D2, C2, C3],
      )(implicit
        ev: (B3 |*| B4) =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (D1 |*| (C2 |*| C3)) = {
        val thiz = ev.biSubst[IXI[A1, A2, A3, A4, B1, B2, *, *]](this)
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
      )(implicit
        ev1: (B1 |*| B2) =:= (B11 |*| B12),
        ev2: (B3 |*| B4) =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ ((C1 |*| C2) |*| (C3 |*| C4)) =
        BiTransferOpt(ev1.biSubst(g1), ev2.biSubst(g2)).ixi_this_ixi(that)

      override def assocLR_this_assocRL[X, Y1, Y2](h: AssocRL[X, (B1 |*| B2), (B3 |*| B4), Y1, Y2]): ((X |*| (A1 |*| A2)) |*| (A3 |*| A4)) ~⚬ ((Y1 |*| Y2) |*| (B3 |*| B4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_assocRL($h)")

      override def assocLR_this_xi[X, Y2, Y3](h: XI[X, (B1 |*| B2), (B3 |*| B4), Y2, Y3]): ((X |*| (A1 |*| A2)) |*| (A3 |*| A4)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        UnhandledCase.raise(s"$h")

      override def assocLR_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[P1, P2, (B1 |*| B2), (B3 |*| B4), Q1, Q2, Q3, Q4]): (((P1 |*| P2) |*| (A1 |*| A2)) |*| (A3 |*| A4)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_ixi")

      override def assocRL_this_assocLR[X, Y2, Y3](h: AssocLR[(B1 |*| B2), (B3 |*| B4), X, Y2, Y3]): ((A1 |*| A2) |*| ((A3 |*| A4) |*| X)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_assocLR($h)")

      override def assocRL_this_ix[X, Y1, Y2](that: IX[(B1 |*| B2), (B3 |*| B4), X, Y1, Y2]): ((A1 |*| A2) |*| ((A3 |*| A4) |*| X)) ~⚬ ((Y1 |*| Y2) |*| (B3 |*| B4)) =
        decompose(AssocRL(g1).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(fst(f1), ix > fst(f2), IXI(h, g2))
        }

      override def assocRL_this_ixi[X1, X2, Y1, Y2, Y3, Y4](h: IXI[(B1 |*| B2), (B3 |*| B4), X1, X2, Y1, Y2, Y3, Y4]): ((A1 |*| A2) |*| ((A3 |*| A4) |*| (X1 |*| X2))) ~⚬ ((Y1 |*| Y2) |*| (Y3 |*| Y4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ixi")

      override def ix_this_assocLR[X, Y2, Y3](that: AssocLR[(B1 |*| B2), (B3 |*| B4), X, Y2, Y3]): (((A1 |*| A2) |*| X) |*| (A3 |*| A4)) ~⚬ ((B1 |*| B2) |*| (Y2 |*| Y3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_assocLR($that)")

      override def ix_this_ix[X, Y1, Y2](that: IX[(B1 |*| B2), (B3 |*| B4), X, Y1, Y2]): (((A1 |*| A2) |*| X) |*| (A3 |*| A4)) ~⚬ ((Y1 |*| Y2) |*| (B3 |*| B4)) =
        decompose(IX(g1).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(ix > fst(f1), fst(f2), IXI(h, g2))
        }

      override def ix_this_ixi[P1, P2, Q1, Q2, Q3, Q4](that: IXI[B1 |*| B2, B3 |*| B4, P1, P2, Q1, Q2, Q3, Q4]): (((A1 |*| A2) |*| (P1 |*| P2)) |*| (A3 |*| A4)) ~⚬ ((Q1 |*| Q2) |*| (Q3 |*| Q4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_ixi")

      override def xi_this_assocRL[X, Y1, Y2](g: AssocRL[X, (B1 |*| B2), (B3 |*| B4), Y1, Y2]): ((A1 |*| A2) |*| (X |*| (A3 |*| A4))) ~⚬ ((Y1 |*| Y2) |*| (B3 |*| B4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_assocRL($g)")

      override def xi_this_xi[X, C2, C3](
        g: XI[X, (B1 |*| B2), (B3 |*| B4), C2, C3],
      ): ((A1 |*| A2) |*| (X |*| (A3 |*| A4))) ~⚬ ((B1 |*| B2) |*| (C2 |*| C3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_xi($g)")

      override def ixi_fstThis_assocLR[P1, P2, Q1, Q2, R2, R3](
        g2: TransferOpt[P1, P2, Q1, Q2],
        that: AssocLR[(B1 |*| B2), (B3 |*| B4), Q1 |*| Q2, R2, R3],
      ): (((A1 |*| A2) |*| P1) |*| ((A3 |*| A4) |*| P2)) ~⚬ ((B1 |*| B2) |*| (R2 |*| R3)) =
        decompose(ixi > par(this.g2.asShuffle, g2.asShuffle) > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(assocLR > snd(f1), assocLR > snd(f2), IXI(this.g1, h))
        }

      override def ixi_sndThis_assocRL[P1, P2, Q1, Q2, R1, R2](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: AssocRL[Q1 |*| Q2, (B1 |*| B2), (B3 |*| B4), R1, R2],
      ): ((P1 |*| (A1 |*| A2)) |*| (P2 |*| (A3 |*| A4))) ~⚬ ((R1 |*| R2) |*| (B3 |*| B4)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_sndThis_assocRL")

      override def ixi_sndThis_xi[P1, P2, Q1, Q2, R2, R3](
        g1: TransferOpt[P1, P2, Q1, Q2],
        that: XI[Q1 |*| Q2, (B1 |*| B2), (B3 |*| B4), R2, R3],
      ): ((P1 |*| (A1 |*| A2)) |*| (P2 |*| (A3 |*| A4))) ~⚬ ((B1 |*| B2) |*| (R2 |*| R3)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_sndThis_xi")

      override def invert: Xfer[(B1 |*| B2), (B3 |*| B4), _, _, A1 |*| A2, A3 |*| A4] =
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

    def swap_then_assocLR[X1, X2, X3, Y2, Y3](
      f: Swap[X1, X2 |*| X3],
      g: AssocLR[X2, X3, X1, Y2, Y3]
    ): (X1 |*| (X2 |*| X3)) ~⚬ (X2 |*| (Y2 |*| Y3)) =
      xi(swap > g.g.asShuffle)

    def swap_then_assocRL[X1, X2, X3, Y1, Y2](
      f: Swap[X1 |*| X2, X3],
      g: AssocRL[X3, X1, X2, Y1, Y2],
    ): ((X1 |*| X2) |*| X3) ~⚬ ((Y1 |*| Y2) |*| X2) =
      ix(swap > g.g.asShuffle)

    def assocLR_then_assocLR[A1, A2, A3, A4, B2, B3, C2, C3](
      f: AssocLR[A1 |*| A2, A3, A4, B2, B3],
      g: AssocLR[A1, A2, B2 |*| B3, C2, C3],
    ): (((A1 |*| A2)|*| A3) |*| A4) ~⚬ (A1 |*| (C2 |*| C3)) =
      decompose(assocLR > snd(f.g.asShuffle) > g.g.asShuffle) match {
        case Decomposition(f1, f2, g) => Xfer(assocLR > snd(f1), f2, AssocLR(g))
      }

    def assocLR_then_assocRL[A1, A2, A3, B2, B3, C1, C2](
      f: AssocLR[A1, A2, A3, B2, B3],
      g: AssocRL[A1, B2, B3, C1, C2],
    ): ((A1 |*| A2) |*| A3) ~⚬ ((C1 |*| C2) |*| B3) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          par(snd(i) > g.g.asShuffle, j)
        case Left(t) =>
          t.assocLR_this_assocRL(g)
      }

    def assocLR_then_xi[A1, A2, A3, B2, B3, C2, C3](
      f: AssocLR[A1, A2, A3, B2, B3],
      g: XI[A1, B2, B3, C2, C3],
    ): ((A1 |*| A2) |*| A3) ~⚬ (B2 |*| (C2 |*| C3)) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          Xfer(snd(i) > swap, j, AssocLR(g.g))
        case Left(t) =>
          t.assocLR_this_xi(g)
      }

    def assocRL_then_assocLR[A1, A2, A3, B1, B2, C2, C3](
      f: AssocRL[A1, A2, A3, B1, B2],
      g: AssocLR[B1, B2, A3, C2, C3],
    ): (A1 |*| (A2 |*| A3)) ~⚬ (B1 |*| (C2 |*| C3)) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          par(i, fst(j) > g.g.asShuffle)
        case Left(t) =>
          t.assocRL_this_assocLR(g)
      }

    def ix_then_assocRL[A1, A2, A3, A4, B1, B2, C1, C2](
      f: IX[A1, A2 |*| A3, A4, B1, B2],
      g: AssocRL[B1 |*| B2, A2, A3, C1, C2],
    ): ((A1 |*| (A2 |*| A3)) |*| A4) ~⚬ ((C1 |*| C2) |*| A3) =
      decompose(IX(f.g).asShuffle > g.g.asShuffle) match {
        case Decomposition(f1, f2, h) => Xfer(assocRL > fst(f1), f2, IX(h))
      }

    def xi_then_assocLR[A1, A2, A3, A4, B2, B3, C2, C3](
      f: XI[A1, A2 |*| A3, A4, B2, B3],
      g: AssocLR[A2, A3, B2 |*| B3, C2, C3],
    ): (A1 |*| ((A2 |*| A3) |*| A4)) ~⚬ (A2 |*| (C2 |*| C3)) =
      decompose(xi > snd(f.g.asShuffle) > g.g.asShuffle) match {
        case Decomposition(f1, f2, g) => Xfer(f1, assocLR > snd(f2), XI(g))
      }

    def xi_then_assocRL[A1, A2, A3, B2, B3, C1, C2](
      f: XI[A1, A2, A3, B2, B3],
      g: AssocRL[A2, B2, B3, C1, C2],
    ): (A1 |*| (A2 |*| A3)) ~⚬ ((C1 |*| C2) |*| B3) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          decompose(swap > g.g.asShuffle) match {
            case Decomposition(f1, f2, h) => Xfer(i > f1, par(f2, j), AssocRL(h))
          }
        case Left(t) =>
          t.xi_this_assocRL(g)
      }

    def xi_then_xi[A1, A2, A3, B2, B3, C2, C3](
      f: XI[A1, A2, A3, B2, B3],
      g: XI[A2, B2, B3, C2, C3],
    ): (A1 |*| (A2 |*| A3)) ~⚬ (B2 |*| (C2 |*| C3)) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          par(i, snd(j) > g.g.asShuffle)
        case Left(t) =>
          t.xi_this_xi(g)
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
          implicitly[(A |*| C) =:= (A |*| C)]
        )
      )
  }
}