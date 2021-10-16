package libretto.impl

import libretto.BiInjective
import libretto.BiInjective._

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
    case class Bimap[X1, X2, Y1, Y2](par: Par[X1, X2, Y1, Y2]) extends Composed[X1 |*| X2, Y1 |*| Y2]

    /** An operator that transfers resources across inputs. */
    case class Xfer[A1, A2, X1, X2, B1, B2](f1: A1 ~⚬ X1, f2: A2 ~⚬ X2, transfer: Transfer[X1, X2, B1, B2]) extends Composed[A1 |*| A2, B1 |*| B2]

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

    def xi[A1, A2, A3, B](g: (A1 |*| A3) ~⚬ B): (A1 |*| (A2 |*| A3)) ~⚬ (A2 |*| B) =
      decompose(g) match {
        case Decomposition(g1, g2, h) => Xfer(g1, snd(g2), Transfer.XI(h))
      }

    def ix[X, Y, Z]: ((X |*| Y) |*| Z) ~⚬ ((X |*| Z) |*| Y) =
      Xfer(Id(), Id(), Transfer.IX(TransferOpt.None()))

    def ix[A1, A2, A3, B](g: (A1 |*| A3) ~⚬ B): ((A1 |*| A2) |*| A3) ~⚬ (B |*| A2) =
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

    def decompose[X1, X2, Z](f: (X1 |*| X2) ~⚬ Z): Decomposition[X1, X2, _, _, Z] =
      f match {
        case Id()               => Decomposition(Id(), Id(), TransferOpt.None())
        case Bimap(Par(f1, f2)) => Decomposition(f1, f2, TransferOpt.None())
        case Xfer(f1, f2, xfer) => Decomposition(f1, f2, xfer)
      }

    case class Decomposition[X1, X2, Y1, Y2, Z](
      f1: X1 ~⚬ Y1,
      f2: X2 ~⚬ Y2,
      g: TransferOpt[Y1 |*| Y2, Z],
    )
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
  }

  object Par {
    def unapply[X1, X2, Y1, Y2](p: Par[X1, X2, Y1, Y2]): (X1 ~⚬ Y1, X2 ~⚬ Y2) =
      p match {
        case Fst(f1) => (f1, Id())
        case Snd(f2) => (Id(), f2)
        case Both(f1, f2) => (f1, f2)
      }
  }

  sealed trait TransferOpt[A, B] {
    def fold[->[_, _]](using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B

    def pairWith[X1, X2, X3, X4, Z](that: TransferOpt[X3 |*| X4, Z])(implicit ev: A =:= (X1 |*| X2)): BiTransferOpt[X1, X2, X3, X4, B, Z]

    def nonePairWith_:[X1, X2, X3, X4](that: TransferOpt.None[X1 |*| X2])(implicit ev: A =:= (X3 |*| X4)): BiTransferOpt[X1, X2, X3, X4, X1 |*| X2, B]

    def swapPairWith_:[X1, X2, X3, X4](that: Transfer.Swap[X1, X2])(implicit ev: A =:= (X3 |*| X4)): BiTransferOpt[X1, X2, X3, X4, X2 |*| X1, B]

    def ixiPairWith_:[X1, X2, X3, X4, X5, X6, Y1, Y2](
      that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2],
    )(implicit
      ev: A =:= (X5 |*| X6),
    ): BiTransferOpt[X1 |*| X2, X3 |*| X4, X5, X6, Y1 |*| Y2, B]

    def asShuffle: A ~⚬ B =
      this match {
        case x: Transfer[_, _, _, _] => Xfer(Id(), Id(), x)
        case TransferOpt.None() => Id()
      }

    def splitOutput[A1, A2](implicit ev: A =:= (A1 |*| A2)): TransferOpt.SplitOutput[A1, A2, _, _, B]
  }

  object TransferOpt {
    sealed trait None0[A, B] extends TransferOpt[A, B] {
      def ev: A =:= B

      override def splitOutput[A1, A2](implicit ev1: A =:= (A1 |*| A2)): TransferOpt.SplitOutput[A1, A2, _, _, B] =
        SplitOutput(None[A1 |*| A2](), ev1.flip.andThen(ev))
    }

    object None0 {
      def apply[A, B](ev: A =:= B): None0[A, B] =
        ev.substituteCo(None[A]())
    }

    case class None[X]() extends None0[X, X] {
      override def fold[->[_, _]](using ev: SymmetricSemigroupalCategory[->, |*|]): X -> X =
        ev.id

      override def ev: X =:= X =
        summon[X =:= X]

      override def pairWith[A1, A2, A3, A4, C](that: TransferOpt[A3 |*| A4, C])(implicit ev: X =:= (A1 |*| A2)): BiTransferOpt[A1, A2, A3, A4, X, C] =
        ev.substituteContra[[x] =>> BiTransferOpt[A1, A2, A3, A4, x, C]](ev.substituteCo(this) nonePairWith_: that)

      override def nonePairWith_:[X1, X2, X3, X4](that: TransferOpt.None[X1 |*| X2])(implicit ev: X =:= (X3 |*| X4)): BiTransferOpt[X1, X2, X3, X4, X1 |*| X2, X] =
        ev.substituteContra[[x] =>> BiTransferOpt[X1, X2, X3, X4, X1 |*| X2, x]](BiTransferOpt.None_None[X1, X2, X3, X4]())

      override def swapPairWith_:[X1, X2, X3, X4](that: Transfer.Swap[X1, X2])(implicit ev: X =:= (X3 |*| X4)): BiTransferOpt[X1, X2, X3, X4, X2 |*| X1, X] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def ixiPairWith_:[X1, X2, X3, X4, X5, X6, Y1, Y2](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2],
      )(implicit
        ev: X =:= (X5 |*| X6),
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, X5, X6, Y1 |*| Y2, X] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")
    }

    def decompose[A1, A2, B1, B2](f: TransferOpt[A1 |*| A2, B1 |*| B2]): Either[Transfer[A1, A2, B1, B2], (Id0[A1, B1], Id0[A2, B2])] =
      f match {
        case t: Transfer[A1, A2, B1, B2] =>
          Left(t)
        case n: TransferOpt.None0[A1 |*| A2, B1 |*| B2] =>
          val (ev1, ev2) = inj.unapply(n.ev)
          Right((Id0(ev1)), Id0(ev2))
      }

    def splitOutput[A1, A2, B](f: TransferOpt[A1 |*| A2, B]): SplitOutput[A1, A2, _, _, B] =
      f.splitOutput[A1, A2]

    case class SplitOutput[A1, A2, B1, B2, B](
      f: TransferOpt[A1 |*| A2, B1 |*| B2],
      ev: (B1 |*| B2) =:= B,
    )
  }

  sealed trait Transfer[A1, A2, B1, B2] extends TransferOpt[A1 |*| A2, B1 |*| B2] {
    import Transfer._

    def after[Z1, Z2](that: Transfer[Z1, Z2, A1, A2]): (Z1 |*| Z2) ~⚬ (B1 |*| B2)

    def thenBi[C1, C2](g1: B1 ~⚬ C1, g2: B2 ~⚬ C2): Xfer[A1, A2, _, _, C1, C2]

    def thenSwap: (A1 |*| A2) ~⚬ (B2 |*| B1)

    def thenAssocLR[B11, B12, C2](
      that: AssocLR[B11, B12, B2, C2],
    )(implicit
      ev: B1 =:= (B11 |*| B12),
    ): (A1 |*| A2) ~⚬ (B11 |*| C2)

    def thenAssocRL[B21, B22, C](
      that: AssocRL[B1, B21, B22, C],
    )(using
      ev: B2 =:= (B21 |*| B22),
    ): (A1 |*| A2) ~⚬ (C |*| B22)

    def thenIX[B11, B12, C](
      that: IX[B11, B12, B2, C],
    )(using
      ev: B1 =:= (B11 |*| B12),
    ): (A1 |*| A2) ~⚬ (C |*| B12)

    def thenXI[B21, B22, C](
      that: XI[B1, B21, B22, C],
    )(implicit
      ev: B2 =:= (B21 |*| B22),
    ): (A1 |*| A2) ~⚬ (B21 |*| C)

    def thenIXI[B11, B12, B21, B22, C, D](
      that: IXI[B11, B12, B21, B22, C, D]
    )(implicit
      ev1: B1 =:= (B11 |*| B12),
      ev2: B2 =:= (B21 |*| B22),
    ): (A1 |*| A2) ~⚬ (C |*| D)

    def assocLR_this_swap[X]: ((X |*| A1) |*| A2) ~⚬ ((B1 |*| B2) |*| X)

    def assocLR_this_assocRL[X, Y](h: AssocRL[X, B1, B2, Y]): ((X |*| A1) |*| A2) ~⚬ (Y |*| B2)

    def assocLR_this_xi[X, Y](h: XI[X, B1, B2, Y]): ((X |*| A1) |*| A2) ~⚬ (B1 |*| Y)

    def assocRL_this_assocLR[X, Y](h: AssocLR[B1, B2, X, Y]): (A1 |*| (A2 |*| X)) ~⚬ (B1 |*| Y)

    def assocRL_this_ix[X, Y](h: IX[B1, B2, X, Y]): (A1 |*| (A2 |*| X)) ~⚬ (Y |*| B2)

    def assocRL_this_ixi[X1, X2, Y1, Y2](h: IXI[B1, B2, X1, X2, Y1, Y2]): (A1 |*| (A2 |*| (X1 |*| X2))) ~⚬ (Y1 |*| Y2)

    def ix_this_swap[X]: ((A1 |*| X) |*| A2) ~⚬ (X |*| (B1 |*| B2))

    def ix_this_assocLR[X, Y](that: AssocLR[B1, B2, X, Y]): ((A1 |*| X) |*| A2) ~⚬ (B1 |*| Y)

    def ix_this_ix[X, Y](that: IX[B1, B2, X, Y]): ((A1 |*| X) |*| A2) ~⚬ (Y |*| B2)

    def xi_this_assocRL[X, Y](g: AssocRL[X, B1, B2, Y]): (A1 |*| (X |*| A2)) ~⚬ (Y |*| B2)

    def xi_this_xi[X, C](g: XI[X, B1, B2, C]): (A1 |*| (X |*| A2)) ~⚬ (B1 |*| C)

    def ixi_fstThis_assocLR[P1, P2, Q, R](
      g2: TransferOpt[P1 |*| P2, Q],
      that: AssocLR[B1, B2, Q, R],
    ): ((A1 |*| P1) |*| (A2 |*| P2)) ~⚬ (B1 |*| R)

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
        case Swap()                         => swap
        case f: AssocLR[x1, x2, x3, y2]     => assocLR[x1, x2, x3] > par(id, f.g.fold)
        case f: AssocRL[x1, x2, x3, y1]     => assocRL[x1, x2, x3] > par(f.g.fold, id)
        case f: IX[x1, x2, x3, y1]          => ix[x1, x2, x3] > par(f.g.fold, id)
        case f: XI[x1, x2, x3, y2]          => xi[x1, x2, x3] > par(id, f.g.fold)
        case f: IXI[x1, x2, x3, x4, y1, y2] => ixi[x1, x2, x3, x4] > par(f.g1.fold, f.g2.fold)
      }
    }

    override def splitOutput[X1, X2](implicit ev: (A1 |*| A2) =:= (X1 |*| X2)): TransferOpt.SplitOutput[X1, X2, _, _, B1 |*| B2] =
      TransferOpt.SplitOutput(
        ev.substituteCo[[x] =>> TransferOpt[x, B1 |*| B2]](this),
        implicitly[(B1 |*| B2) =:= (B1 |*| B2)],
      )


    final override def pairWith[X1, X2, X3, X4, Z](that: TransferOpt[X3 |*| X4, Z])(implicit ev: (A1 |*| A2) =:= (X1 |*| X2)): BiTransferOpt[X1, X2, X3, X4, B1 |*| B2, Z] =
      ev.biSubst[Transfer[*, *, B1, B2]](this) _pairWith that

    def _pairWith[X3, X4, Z](that: TransferOpt[X3 |*| X4, Z]): BiTransferOpt[A1, A2, X3, X4, B1 |*| B2, Z]

    final override def nonePairWith_:[X1, X2, X3, X4](that: TransferOpt.None[X1 |*| X2])(implicit ev: (A1 |*| A2) =:= (X3 |*| X4)): BiTransferOpt[X1, X2, X3, X4, X1 |*| X2, B1 |*| B2] =
      that _nonePairWith_: ev.biSubst[Transfer[*, *, B1, B2]](this)

    def _nonePairWith_:[X1, X2](that: TransferOpt.None[X1 |*| X2]): BiTransferOpt[X1, X2, A1, A2, X1 |*| X2, B1 |*| B2]

    final override def swapPairWith_:[X1, X2, X3, X4](that: Transfer.Swap[X1, X2])(implicit ev: (A1 |*| A2) =:= (X3 |*| X4)): BiTransferOpt[X1, X2, X3, X4, X2 |*| X1, B1 |*| B2] =
      that _swapPairWith_: ev.biSubst[Transfer[*, *, B1, B2]](this)

    def _swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1, A2, X2 |*| X1, B1 |*| B2]

    final override def ixiPairWith_:[X1, X2, X3, X4, X5, X6, Y1, Y2](
      that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2],
    )(implicit
      ev: (A1 |*| A2) =:= (X5 |*| X6),
    ): BiTransferOpt[X1 |*| X2, X3 |*| X4, X5, X6, Y1 |*| Y2, B1 |*| B2] =
      that _ixiPairWith_: ev.biSubst[Transfer[*, *, B1, B2]](this)

    def _ixiPairWith_:[X1, X2, X3, X4, Y1, Y2](that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2]): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1, A2, Y1 |*| Y2, B1 |*| B2]
  }

  object Transfer {
    case class Swap[X1, X2]() extends Transfer[X1, X2, X2, X1] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, X1, X2]): (Z1 |*| Z2) ~⚬ (X2 |*| X1) =
        that.thenSwap

      override def thenBi[C1, C2](g1: X2 ~⚬ C1, g2: X1 ~⚬ C2): Xfer[X1, X2, _, _, C1, C2] =
        Xfer(g2, g1, Swap())

      override def thenSwap: (X1 |*| X2) ~⚬ (X1 |*| X2) =
        Id()

      override def thenAssocLR[X21, X22, C2](
        that: AssocLR[X21, X22, X1, C2],
      )(implicit
        ev: X2 =:= (X21 |*| X22),
      ): (X1 |*| X2) ~⚬ (X21 |*| C2) = {
        val res = swap_then_assocLR(ev.substituteCo(this), that)
        ev.substituteContra[[x] =>> (X1 |*| x) ~⚬ (X21 |*| C2)](res)
      }

      override def thenAssocRL[B21, B22, C](
        that: AssocRL[X2, B21, B22, C],
      )(using
        ev: X1 =:= (B21 |*| B22),
      ): (X1 |*| X2) ~⚬ (C |*| B22) = {
        val res = swap_then_assocRL(ev.substituteCo[[x] =>> Swap[x, X2]](this), that)
        ev.substituteContra[[x] =>> (x |*| X2) ~⚬ (C |*| B22)](res)
      }

      override def thenIX[B11, B12, C](
        that: IX[B11, B12, X1, C],
      )(using
        ev: X2 =:= (B11 |*| B12),
      ): (X1 |*| X2) ~⚬ (C |*| B12) =
        decompose(swap > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, Id0(ev) > fst(f2), AssocRL(h))
        }

      override def thenXI[X11, X12, C](
        that: XI[X2, X11, X12, C],
      )(implicit
        ev: X1 =:= (X11 |*| X12),
      ): (X1 |*| X2) ~⚬ (X11 |*| C) =
        decompose(swap > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(Id0(ev) > snd(f1), f2, AssocLR(h))
        }

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: X2 =:= (B11 |*| B12),
        ev2: X1 =:= (B21 |*| B22),
      ): (X1 |*| X2) ~⚬ (C |*| D) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenIXI($that)")

      override def assocLR_this_swap[X]: ((X |*| X1) |*| X2) ~⚬ ((X2 |*| X1) |*| X) =
        Xfer(swap, id, IX(Swap()))

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, X2, X1, Y]): ((X |*| X1) |*| X2) ~⚬ (Y |*| X1) =
        IX[X, X1, X2, Y](h.g).asShuffle

      override def assocLR_this_xi[X, Y](h: XI[X, X2, X1, Y]): ((X |*| X1) |*| X2) ~⚬ (X2 |*| Y) =
        Xfer(h.g.asShuffle, id, Swap())

      override def assocRL_this_assocLR[X, Y](h: AssocLR[X2, X1, X, Y]): (X1 |*| (X2 |*| X)) ~⚬ (X2 |*| Y) =
        XI(h.g).asShuffle

      override def assocRL_this_ix[X, Y](h: IX[X2, X1, X, Y]): (X1 |*| (X2 |*| X)) ~⚬ (Y |*| X1) =
        Xfer(id, h.g.asShuffle, Swap())

      override def assocRL_this_ixi[X3, X4, Y1, Y2](h: IXI[X2, X1, X3, X4, Y1, Y2]): (X1 |*| (X2 |*| (X3 |*| X4))) ~⚬ (Y1 |*| Y2) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ixi")

      override def ix_this_swap[X]: ((X1 |*| X) |*| X2) ~⚬ (X |*| (X2 |*| X1)) =
        Xfer(swap, id, AssocLR(Swap()))

      override def ix_this_assocLR[X, Y](that: AssocLR[X2, X1, X, Y]): ((X1 |*| X) |*| X2) ~⚬ (X2 |*| Y) =
        Xfer(that.g.asShuffle, id, Swap())

      override def ix_this_ix[X, Y](that: IX[X2, X1, X, Y]): ((X1 |*| X) |*| X2) ~⚬ (Y |*| X1) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_ix($that)")

      override def xi_this_assocRL[X, Y](g: AssocRL[X, X2, X1, Y]): (X1 |*| (X |*| X2)) ~⚬ (Y |*| X1) =
        Xfer(Id(), g.g.asShuffle, Swap())

      override def xi_this_xi[X, C](g: XI[X, X2, X1, C]): (X1 |*| (X |*| X2)) ~⚬ (X2 |*| C) =
        decompose(swap > g.g.asShuffle) match {
          case Decomposition(h1, h2, h) => Xfer(h1, fst(h2) > swap, XI(h))
        }

      override def ixi_fstThis_assocLR[P1, P2, Q, R](
        g2: TransferOpt[P1 |*| P2, Q],
        that: AssocLR[X2, X1, Q, R],
      ): ((X1 |*| P1) |*| (X2 |*| P2)) ~⚬ (X2 |*| R) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_fstThis_assocLR")

      override def invert: Xfer[X2, X1, _, _, X1, X2] =
        Xfer(Id(), Id(), Swap())

      override def _ixiPairWith_:[A1, A2, A3, A4, B1, B2](
        that: Transfer.IXI[A1, A2, A3, A4, B1, B2],
      ): BiTransferOpt[A1 |*| A2, A3 |*| A4, X1, X2, B1 |*| B2, X2 |*| X1] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:(that)")

      override def _nonePairWith_:[A1, A2](that: TransferOpt.None[A1 |*| A2]): BiTransferOpt[A1, A2, X1, X2, A1 |*| A2, X2 |*| X1] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def _swapPairWith_:[A1, A2](that: Transfer.Swap[A1, A2]): BiTransferOpt[A1, A2, X1, X2, A2 |*| A1, X2 |*| X1] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def _pairWith[X3, X4, Z](that: TransferOpt[X3 |*| X4, Z]): BiTransferOpt[X1, X2, X3, X4, X2 |*| X1, Z] =
        this swapPairWith_: that
    }

    case class AssocLR[A1, A2, A3, B2](g: TransferOpt[A2 |*| A3, B2]) extends Transfer[A1 |*| A2, A3, A1, B2] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1 |*| A2, A3]): (Z1 |*| Z2) ~⚬ (A1 |*| B2) =
        that thenAssocLR this

      override def thenBi[C1, C2](g1: A1 ~⚬ C1, g2: B2 ~⚬ C2): Xfer[A1 |*| A2, A3, _, _, C1, C2] =
        decompose(g.asShuffle > g2) match {
          case Decomposition(f1, f2, g) => Xfer(par(g1, f1), f2, AssocLR(g))
        }

      override def thenSwap: ((A1 |*| A2) |*| A3) ~⚬ (B2 |*| A1) =
        TransferOpt.splitOutput(g) match {
          case TransferOpt.SplitOutput(g, ev) =>
            TransferOpt.decompose(g) match {
              case Right((i, j)) => par(snd(i) > swap, j) > ix > ~⚬.fst(~⚬.Id0(ev))
              case Left(t) => t.assocLR_this_swap > ~⚬.fst(~⚬.Id0(ev))
            }
        }

      override def thenAssocLR[A11, A12, C2](
        that: AssocLR[A11, A12, B2, C2],
      )(implicit
        ev: A1 =:= (A11 |*| A12),
      ): ((A1 |*| A2) |*| A3) ~⚬ (A11 |*| C2) = {
        val res = assocLR_then_assocLR(ev.substituteCo[[x] =>> AssocLR[x, A2, A3, B2]](this), that)
        ev.substituteContra[[x] =>> ((x |*| A2) |*| A3) ~⚬ (A11 |*| C2)](res)
      }

      override def thenAssocRL[B21, B22, C](
        that: AssocRL[A1, B21, B22, C],
      )(using
        ev: B2 =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (C |*| B22) =
        assocLR_then_assocRL(ev.substituteCo[[x] =>> AssocLR[A1, A2, A3, x]](this), that)

      override def thenIX[B11, B12, C](
        that: IX[B11, B12, B2, C],
      )(using
        ev: A1 =:= (B11 |*| B12),
      ): ((A1 |*| A2) |*| A3) ~⚬ (C |*| B12) =
        decompose(AssocLR(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(fst(Id0(ev)) > ix > fst(f1), f2, IX(h))
        }

      override def thenXI[B21, B22, C](
        that: XI[A1, B21, B22, C],
      )(implicit
        ev: B2 =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (B21 |*| C) =
        assocLR_then_xi(ev.substituteCo[[x] =>> AssocLR[A1, A2, A3, x]](this), that)

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: A1 =:= (B11 |*| B12),
        ev2: B2 =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (C |*| D) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenIXI($that)")

      override def assocLR_this_swap[X]: ((X |*| (A1 |*| A2)) |*| A3) ~⚬ ((A1 |*| B2) |*| X) =
        Xfer(swap, id, IX(AssocLR(g)))

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, A1, B2, Y]): ((X |*| (A1 |*| A2)) |*| A3) ~⚬ (Y |*| B2) =
        Xfer(AssocRL(h.g).asShuffle, Id(), AssocLR(g))

      override def assocLR_this_xi[X, Y](h: XI[X, A1, B2, Y]): ((X |*| (A1 |*| A2)) |*| A3) ~⚬ (A1 |*| Y) =
        UnhandledCase.raise(s"$h")

      override def assocRL_this_assocLR[X, Y](h: AssocLR[A1, B2, X, Y]): ((A1 |*| A2) |*| (A3 |*| X)) ~⚬ (A1 |*| Y) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_assocLR($h)")

      override def assocRL_this_ix[X, Y](h: IX[A1, B2, X, Y]): ((A1 |*| A2) |*| (A3 |*| X)) ~⚬ (Y |*| B2) =
        Xfer(id, swap, IXI(h.g, g))

      override def assocRL_this_ixi[X1, X2, Y1, Y2](h: IXI[A1, B2, X1, X2, Y1, Y2]): ((A1 |*| A2) |*| (A3 |*| (X1 |*| X2))) ~⚬ (Y1 |*| Y2) =
        decompose(assocRL > fst(g.asShuffle) > h.g2.asShuffle) match {
          case Decomposition(f1, f2, g2) => Xfer(snd(f1), xi > snd(f2), IXI(h.g1, g2))
        }

      override def ix_this_swap[X]: (((A1 |*| A2) |*| X) |*| A3) ~⚬ (X |*| (A1 |*| B2)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_swap")

      override def ix_this_assocLR[X, Y](that: AssocLR[A1, B2, X, Y]): (((A1 |*| A2) |*| X) |*| A3) ~⚬ (A1 |*| Y) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_assocLR($that)")

      override def ix_this_ix[X, Y](h: IX[A1, B2, X, Y]): (((A1 |*| A2) |*| X) |*| A3) ~⚬ (Y |*| B2) =
        Xfer(IX(h.g).asShuffle, id, AssocLR(g))

      override def xi_this_assocRL[X, Y](h: AssocRL[X, A1, B2, Y]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ (Y |*| B2) =
        decompose(swap > h.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(fst(f1), fst(f2), IXI(h, g))
        }

      override def xi_this_xi[X, C](g: XI[X, A1, B2, C]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ (A1 |*| C) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_xi($g)")

      override def ixi_fstThis_assocLR[P1, P2, Q, R](
        g2: TransferOpt[P1 |*| P2, Q],
        that: AssocLR[A1, B2, Q, R],
      ): (((A1 |*| A2) |*| P1) |*| (A3 |*| P2)) ~⚬ (A1 |*| R) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_fstThis_assocLR")

      override def invert: Xfer[A1, B2, _, _, A1 |*| A2, A3] =
        Xfer(id, g.asShuffle.invert, AssocRL(TransferOpt.None()))

      override def _ixiPairWith_:[X1, X2, X3, X4, Y1, Y2](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1 |*| A2, A3, Y1 |*| Y2, A1 |*| B2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")

      override def _nonePairWith_:[X1, X2](that: TransferOpt.None[X1 |*| X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3, X1 |*| X2, A1 |*| B2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def _swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3, X2 |*| X1, A1 |*| B2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def _pairWith[X3, X4, Z](that: TransferOpt[X3 |*| X4, Z]): BiTransferOpt[A1 |*| A2, A3, X3, X4, A1 |*| B2, Z] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.pairWith($that)")
    }

    case class AssocRL[A1, A2, A3, B](g: TransferOpt[A1 |*| A2, B]) extends Transfer[A1, A2 |*| A3, B, A3] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1, A2 |*| A3]): (Z1 |*| Z2) ~⚬ (B |*| A3) =
        that.thenAssocRL(this)

      override def thenBi[C1, C2](g1: B ~⚬ C1, g2: A3 ~⚬ C2): Xfer[A1, A2 |*| A3, _, _, C1, C2] =
        decompose(g.asShuffle > g1) match {
          case Decomposition(f1, f2, h) => Xfer(f1, par(f2, g2), AssocRL(h))
        }

      override def thenSwap: (A1 |*| (A2 |*| A3)) ~⚬ (A3 |*| B) =
        decompose(g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, fst(f2) > swap, XI(h))
        }

      override def thenAssocLR[D1, D2, C2](
        that: AssocLR[D1, D2, A3, C2],
      )(implicit
        ev: B =:= (D1 |*| D2),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (D1 |*| C2) =
        assocRL_then_assocLR(ev.substituteCo[[x] =>> AssocRL[A1, A2, A3, x]](this), that)

      override def thenAssocRL[B3, B4, C](
        that: AssocRL[B, B3, B4, C],
      )(using
        ev: A3 =:= (B3 |*| B4),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (C |*| B4) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenAssocRL($that)")

      override def thenIX[B11, B12, C](
        that: IX[B11, B12, A3, C],
      )(using
        ev: B =:= (B11 |*| B12),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (C |*| B12) =
        TransferOpt.splitOutput(g) match {
          case TransferOpt.SplitOutput(g, ev0) =>
            TransferOpt.decompose(g) match {
              case Right((i, j)) =>
                val (ev1, ev2) = inj.unapply(ev0 andThen ev)
                Xfer(ev1.substituteCo(i), fst(ev2.substituteCo(j)) > swap, AssocRL(that.g))
              case Left(t) =>
                (t to (ev0 andThen ev)).assocRL_this_ix(that)
            }
        }

      override def thenXI[A31, A32, C](
        that: XI[B, A31, A32, C],
      )(implicit
        ev: A3 =:= (A31 |*| A32),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (A31 |*| C) =
        decompose(assocRL > fst(g.asShuffle) > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) =>
            Xfer(f1, snd(id[A3].to[A31 |*| A32]) > xi > snd(f2), XI(h))
        }

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: B =:= (B11 |*| B12),
        ev2: A3 =:= (B21 |*| B22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (C |*| D) = {
        val thiz: AssocRL[A1, A2, A3, B11 |*| B12] = ev1.substituteCo(this)
        TransferOpt.decompose(thiz.g) match {
          case Right((i, j)) => Xfer(i, par(j, Id0(ev2)) > XI(that.g2).asShuffle, AssocRL(that.g1))
          case Left(t)       => snd(snd(Id0(ev2))) > t.assocRL_this_ixi(that)
        }
      }

      override def assocLR_this_swap[X]: ((X |*| A1) |*| (A2 |*| A3)) ~⚬ ((B |*| A3) |*| X) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_swap")

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, B, A3, Y]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ (Y |*| A3) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_assocRL($h)")

      override def assocLR_this_xi[X, Y](h: XI[X, B, A3, Y]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ (B |*| Y) =
        Xfer(swap, id, IXI(g, h.g))

      override def assocRL_this_assocLR[X, Y](h: AssocLR[B, A3, X, Y]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ (B |*| Y) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_assocLR($h)")

      override def assocRL_this_ix[X, Y](h: IX[B, A3, X, Y]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ (Y |*| A3) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ix($h)")

      override def assocRL_this_ixi[X1, X2, Y1, Y2](h: IXI[B, A3, X1, X2, Y1, Y2]): (A1 |*| ((A2 |*| A3) |*| (X1 |*| X2))) ~⚬ (Y1 |*| Y2) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ixi")

      override def xi_this_assocRL[X, Y](h: AssocRL[X, B, A3, Y]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ (Y |*| A3) =
        decompose(XI(g).asShuffle > h.g.asShuffle) match {
          case Decomposition(h1, h2, h) => Xfer(h1, assocRL > fst(h2), AssocRL(h))
        }

      override def ix_this_swap[X]: ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ (X |*| (B |*| A3)) =
        Xfer(swap, id, AssocLR(AssocRL(g)))

      override def ix_this_assocLR[X, Y](that: AssocLR[B, A3, X, Y]): ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ (B |*| Y) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_assocLR($that)")

      override def ix_this_ix[X, Y](that: IX[B, A3, X, Y]): ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ (Y |*| A3) =
        decompose(IX(g).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, fst(f2), AssocRL(h))
        }

      override def xi_this_xi[X, C](h: XI[X, B, A3, C]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ (B |*| C) =
        Xfer(Id(), XI(h.g).asShuffle, AssocRL(g))

      override def ixi_fstThis_assocLR[P1, P2, Q, R](
        g2: TransferOpt[P1 |*| P2, Q],
        that: AssocLR[B, A3, Q, R],
      ): ((A1 |*| P1) |*| ((A2 |*| A3) |*| P2)) ~⚬ (B |*| R) =
        decompose(XI(g2).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(snd(f1), assocLR > snd(f2), IXI(g, h))
        }

      override def invert: Xfer[B, A3, _, _, A1, A2 |*| A3] =
        Xfer(g.asShuffle.invert, id, AssocLR(TransferOpt.None()))

      override def _ixiPairWith_:[X1, X2, X3, X4, Y1, Y2](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1, A2 |*| A3, Y1 |*| Y2, B |*| A3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")

      override def _nonePairWith_:[X1, X2](that: TransferOpt.None[X1 |*| X2]): BiTransferOpt[X1, X2, A1, A2 |*| A3, X1 |*| X2, B |*| A3] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def _swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1, A2 |*| A3, X2 |*| X1, B |*| A3] =
        BiTransferOpt.Swap_AssocRL(that, this)

      override def _pairWith[X3, X4, Z](that: TransferOpt[X3 |*| X4, Z]): BiTransferOpt[A1, A2 |*| A3, X3, X4, B |*| A3, Z] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.pairWith($that)")
    }

    case class IX[A1, A2, A3, B](g: TransferOpt[A1 |*| A3, B]) extends Transfer[A1 |*| A2, A3, B, A2] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1 |*| A2, A3]): (Z1 |*| Z2) ~⚬ (B |*| A2) =
        that.thenIX(this)

      override def thenBi[C1, C2](g1: B ~⚬ C1, g2: A2 ~⚬ C2): Xfer[A1 |*| A2, A3, _, _, C1, C2] =
        decompose(g.asShuffle > g1) match {
          case Decomposition(f1, f2, h) => Xfer(par(f1, g2), f2, IX(h))
        }

      override def thenSwap: ((A1 |*| A2) |*| A3) ~⚬ (A2 |*| B) =
        TransferOpt.splitOutput(g) match {
          case TransferOpt.SplitOutput(g, ev) =>
            TransferOpt.decompose(g) match {
              case Right((i, j)) => Xfer(fst(i) > swap, j, AssocLR(TransferOpt.None0(ev)))
              case Left(t)       => t.ix_this_swap > snd(Id0(ev))
            }
        }

      override def thenAssocLR[D1, D2, C2](
        that: AssocLR[D1, D2, A2, C2],
      )(implicit
        ev: B =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| A3) ~⚬ (D1 |*| C2) =
        TransferOpt.decompose(ev.substituteCo(g)) match {
          case Right((i, j)) =>
            decompose(swap > that.g.asShuffle) match {
              case Decomposition(f1, f2, h) => Xfer(par(i, f1), j > f2, AssocLR(h))
            }
          case Left(t) =>
            t.ix_this_assocLR(that)
        }

      override def thenAssocRL[X1, X2, C](
        that: AssocRL[B, X1, X2, C],
      )(using
        ev: A2 =:= (X1 |*| X2),
      ): ((A1 |*| A2) |*| A3) ~⚬ (C |*| X2) = {
        val res = ix_then_assocRL(ev.substituteCo[[x] =>> IX[A1, x, A3, B]](this), that)
        ev.substituteContra[[x] =>> ((A1 |*| x) |*| A3) ~⚬ (C |*| X2)](res)
      }

      override def thenIX[B11, B12, C](
        that: IX[B11, B12, A2, C],
      )(using
        ev: B =:= (B11 |*| B12),
      ): ((A1 |*| A2) |*| A3) ~⚬ (C |*| B12) =
        TransferOpt.splitOutput(g) match {
          case TransferOpt.SplitOutput(g, ev0) =>
            TransferOpt.decompose(g) match {
              case Right((i, j)) =>
                implicit val (ev1, ev2) = inj.unapply(ev0 andThen ev)
                par(
                  fst(i.to[B11]) > that.g.asShuffle,
                  j.to[B12],
                )
              case Left(t) =>
                t.to[B11, B12](ev0 andThen ev).ix_this_ix(that)
            }
        }

      override def thenXI[A21, A22, C](
        that: XI[B, A21, A22, C],
      )(implicit
        ev: A2 =:= (A21 |*| A22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (A21 |*| C) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenXI($that)")

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: B =:= (B11 |*| B12),
        ev2: A2 =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (C |*| D) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenIXI($that)")

      override def assocLR_this_swap[X]: ((X |*| (A1 |*| A2)) |*| A3) ~⚬ ((B |*| A2) |*| X) =
        Xfer(swap, id, IX(IX(g)))

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, B, A2, Y]): ((X |*| (A1 |*| A2)) |*| A3) ~⚬ (Y |*| A2) =
        decompose(AssocLR(g).asShuffle > h.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(assocRL > fst(f1), f2, IX(h))
        }

      override def assocLR_this_xi[X, Y](h: XI[X, B, A2, Y]): ((X |*| (A1 |*| A2)) |*| A3) ~⚬ (B |*| Y) =
        UnhandledCase.raise(s"$h")

      override def assocRL_this_assocLR[X, Y](h: AssocLR[B, A2, X, Y]): ((A1 |*| A2) |*| (A3 |*| X)) ~⚬ (B |*| Y) =
        IXI[A1, A2, A3, X, B, Y](g, h.g).asShuffle

      override def assocRL_this_ix[X, Y](h: IX[B, A2, X, Y]): ((A1 |*| A2) |*| (A3 |*| X)) ~⚬ (Y |*| A2) =
        decompose(assocRL > fst(g.asShuffle) > h.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(fst(f1), f2, IX(h))
        }

      override def assocRL_this_ixi[X1, X2, Y1, Y2](h: IXI[B, A2, X1, X2, Y1, Y2]): ((A1 |*| A2) |*| (A3 |*| (X1 |*| X2))) ~⚬ (Y1 |*| Y2) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ixi")

      override def ix_this_swap[X]: (((A1 |*| A2) |*| X) |*| A3) ~⚬ (X |*| (B |*| A2)) =
        decompose(IX(g).asShuffle: ((A1 |*| A2) |*| A3) ~⚬ (B |*| A2)) match {
          case Decomposition(f1, f2, h) =>
            Xfer(swap > snd(f1), f2, AssocLR(h))
        }

      override def ix_this_assocLR[X, Y](that: AssocLR[B, A2, X, Y]): (((A1 |*| A2) |*| X) |*| A3) ~⚬ (B |*| Y) =
        Xfer(AssocLR(that.g).asShuffle, id, IX(g))

      override def ix_this_ix[X, Y](that: IX[B, A2, X, Y]): (((A1 |*| A2) |*| X) |*| A3) ~⚬ (Y |*| A2) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_ix($that)")

      override def xi_this_assocRL[X, Y](h: AssocRL[X, B, A2, Y]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ (Y |*| A2) =
        ix(XI(g).asShuffle > h.g.asShuffle)

      override def xi_this_xi[X, C](h: XI[X, B, A2, C]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ (B |*| C) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_xi($h)")

      override def ixi_fstThis_assocLR[P1, P2, Q, R](
        g2: TransferOpt[P1 |*| P2, Q],
        that: AssocLR[B, A2, Q, R],
      ): (((A1 |*| A2) |*| P1) |*| (A3 |*| P2)) ~⚬ (B |*| R) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_fstThis_assocLR")

      override def invert: Xfer[B, A2, _, _, A1 |*| A2, A3] =
        Xfer(g.asShuffle.invert, id, IX(TransferOpt.None()))

      override def _ixiPairWith_:[X1, X2, X3, X4, Y1, Y2](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1 |*| A2, A3, Y1 |*| Y2, B |*| A2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")

      override def _nonePairWith_:[X1, X2](that: TransferOpt.None[X1 |*| X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3, X1 |*| X2, B |*| A2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def _swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3, X2 |*| X1, B |*| A2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def _pairWith[X3, X4, Z](that: TransferOpt[X3 |*| X4, Z]): BiTransferOpt[A1 |*| A2, A3, X3, X4, B |*| A2, Z] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.pairWith($that)")
    }

    case class XI[A1, A2, A3, B2](g: TransferOpt[A1 |*| A3, B2]) extends Transfer[A1, A2 |*| A3, A2, B2] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1, A2 |*| A3]): (Z1 |*| Z2) ~⚬ (A2 |*| B2) =
        that thenXI this

      override def thenBi[C1, C2](g1: A2 ~⚬ C1, g2: B2 ~⚬ C2): Xfer[A1, A2 |*| A3, _, _, C1, C2] =
        decompose(g.asShuffle > g2) match {
          case Decomposition(f1, f2, h) => Xfer(f1, par(g1, f2), XI(h))
        }

      override def thenSwap: (A1 |*| (A2 |*| A3)) ~⚬ (B2 |*| A2) =
        Xfer(Id(), swap, AssocRL(g))

      override def thenAssocLR[A21, A22, C2](
        that: AssocLR[A21, A22, B2, C2],
      )(implicit
        ev: A2 =:= (A21 |*| A22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (A21 |*| C2) = {
        val res = xi_then_assocLR(ev.substituteCo[[x] =>> XI[A1, x, A3, B2]](this), that)
        ev.substituteContra[[x] =>> (A1 |*| (x |*| A3)) ~⚬ (A21 |*| C2)](res)
      }

      override def thenAssocRL[B21, B22, C](
        that: AssocRL[A2, B21, B22, C],
      )(using
        ev: B2 =:= (B21 |*| B22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (C |*| B22) =
        xi_then_assocRL(ev.substituteCo[[x] =>> XI[A1, A2, A3, x]](this), that)

      override def thenIX[B11, B12, C](
        that: IX[B11, B12, B2, C],
      )(using
        ev: A2 =:= (B11 |*| B12),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (C |*| B12) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenIX($that)")

      override def thenXI[B21, B22, C](
        that: XI[A2, B21, B22, C],
      )(implicit
        ev: B2 =:= (B21 |*| B22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (B21 |*| C) =
        xi_then_xi(ev.substituteCo[[x] =>> XI[A1, A2, A3, x]](this), that)

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: A2 =:= (B11 |*| B12),
        ev2: B2 =:= (B21 |*| B22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (C |*| D) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenIXI($that)")

      override def assocLR_this_swap[X]: ((X |*| A1) |*| (A2 |*| A3)) ~⚬ ((A2 |*| B2) |*| X) =
        Xfer(swap, id, IX(XI(g)))

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, A2, B2, Y]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ (Y |*| B2) =
        IXI(h.g, g).asShuffle

      override def assocLR_this_xi[X, Y](h: XI[X, A2, B2, Y]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ (A2 |*| Y) =
        UnhandledCase.raise(s"$h")

      override def assocRL_this_assocLR[X, Y](h: AssocLR[A2, B2, X, Y]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ (A2 |*| Y) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_assocLR($h)")

      override def assocRL_this_ix[X, Y](h: IX[A2, B2, X, Y]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ (Y |*| B2) =
        Xfer(id, IX(h.g).asShuffle, XI(g))

      override def assocRL_this_ixi[X1, X2, Y1, Y2](h: IXI[A2, B2, X1, X2, Y1, Y2]): (A1 |*| ((A2 |*| A3) |*| (X1 |*| X2))) ~⚬ (Y1 |*| Y2) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ixi")

      override def ix_this_swap[X]: ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ (X |*| (A2 |*| B2)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_swap")

      override def ix_this_assocLR[X, Y](that: AssocLR[A2, B2, X, Y]): ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ (A2 |*| Y) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_assocLR($that)")

      override def ix_this_ix[X, Y](that: IX[A2, B2, X, Y]): ((A1 |*| X) |*| (A2 |*| A3)) ~⚬ (Y |*| B2) =
        decompose(swap > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(swap > fst(f1), fst(f2), IXI(h, g))
        }

      override def xi_this_assocRL[X, Y](h: AssocRL[X, A2, B2, Y]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ (Y |*| B2) =
        Xfer(Id(), AssocRL(h.g).asShuffle, XI(g))

      override def xi_this_xi[X, C](g: XI[X, A2, B2, C]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ (A2 |*| C) =
        decompose(xi(this.g.asShuffle) > g.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, xi(f2), XI(h))
        }

      override def ixi_fstThis_assocLR[P1, P2, Q, R](
        g2: TransferOpt[P1 |*| P2, Q],
        that: AssocLR[A2, B2, Q, R],
      ): ((A1 |*| P1) |*| ((A2 |*| A3) |*| P2)) ~⚬ (A2 |*| R) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_fstThis_assocLR")

      override def invert: Xfer[A2, B2, _, _, A1, A2 |*| A3] =
        Xfer(id, g.asShuffle.invert, XI(TransferOpt.None()))

      override def _ixiPairWith_:[X1, X2, X3, X4, Y1, Y2](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1, A2 |*| A3, Y1 |*| Y2, A2 |*| B2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixiPairWith_:($that)")

      override def _nonePairWith_:[X1, X2](that: TransferOpt.None[X1 |*| X2]): BiTransferOpt[X1, X2, A1, A2 |*| A3, X1 |*| X2, (A2 |*| B2)] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def _swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1, A2 |*| A3, X2 |*| X1, A2 |*| B2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def _pairWith[X3, X4, Z](that: TransferOpt[X3 |*| X4, Z]): BiTransferOpt[A1, A2 |*| A3, X3, X4, A2 |*| B2, Z] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.pairWith($that)")
    }

    case class IXI[A1, A2, A3, A4, B1, B2](
      g1: TransferOpt[A1 |*| A3, B1],
      g2: TransferOpt[A2 |*| A4, B2],
    ) extends Transfer[A1 |*| A2, A3 |*| A4, B1, B2] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1 |*| A2, A3 |*| A4]): (Z1 |*| Z2) ~⚬ (B1 |*| B2) =
        that thenIXI this

      override def thenBi[C1, C2](h1: B1 ~⚬ C1, h2: B2 ~⚬ C2): Xfer[A1 |*| A2, A3 |*| A4, _, _, C1, C2] =
        (decompose(g1.asShuffle > h1), decompose(g2.asShuffle > h2)) match {
          case (Decomposition(g11, g12, h1), Decomposition(g21, g22, h2)) =>
            Xfer(par(g11, g21), par(g12, g22), IXI(h1, h2))
        }

      override def thenSwap: ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (B2 |*| B1) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenSwap")

      override def thenAssocLR[D1, D2, C2](
        that: AssocLR[D1, D2, B2, C2],
      )(implicit
        ev: B1 =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (D1 |*| C2) = {
        val thiz = ev.substituteCo[IXI[A1, A2, A3, A4, *, B2]](this)
        TransferOpt.decompose(thiz.g1) match {
          case Right((i, j)) =>
            decompose(XI(thiz.g2).asShuffle > that.g.asShuffle) match {
              case Decomposition(f1, f2, h) => Xfer(par(i, f1), fst(j) > f2, AssocLR(h))
            }
          case Left(t) =>
            t.ixi_fstThis_assocLR(thiz.g2, that)
        }
      }

      override def thenAssocRL[D1, D2, C](
        that: AssocRL[B1, D1, D2, C],
      )(using
        ev: B2 =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (C |*| D2) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenAssocRL($that)")

      override def thenIX[B11, B12, C](
        that: IX[B11, B12, B2, C],
      )(using
        ev: B1 =:= (B11 |*| B12),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (C |*| B12) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.thenIX($that)")

      override def thenXI[D1, D2, C](
        that: XI[B1, D1, D2, C],
      )(implicit
        ev: B2 =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (D1 |*| C) =
        BiTransferOpt(g1, g2).ixi_this_xi(that)

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: B1 =:= (B11 |*| B12),
        ev2: B2 =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (C |*| D) =
        BiTransferOpt(g1, g2).ixi_this_ixi(that)

      override def assocLR_this_swap[X]: ((X |*| (A1 |*| A2)) |*| (A3 |*| A4)) ~⚬ ((B1 |*| B2) |*| X) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_swap")

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, B1, B2, Y]): ((X |*| (A1 |*| A2)) |*| (A3 |*| A4)) ~⚬ (Y |*| B2) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocLR_this_assocRL($h)")

      override def assocLR_this_xi[X, Y](h: XI[X, B1, B2, Y]): ((X |*| (A1 |*| A2)) |*| (A3 |*| A4)) ~⚬ (B1 |*| Y) =
        UnhandledCase.raise(s"$h")

      override def assocRL_this_assocLR[X, Y](h: AssocLR[B1, B2, X, Y]): ((A1 |*| A2) |*| ((A3 |*| A4) |*| X)) ~⚬ (B1 |*| Y) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_assocLR($h)")

      override def assocRL_this_ix[X, Y](h: IX[B1, B2, X, Y]): ((A1 |*| A2) |*| ((A3 |*| A4) |*| X)) ~⚬ (Y |*| B2) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ix($h)")

      override def assocRL_this_ixi[X1, X2, Y1, Y2](h: IXI[B1, B2, X1, X2, Y1, Y2]): ((A1 |*| A2) |*| ((A3 |*| A4) |*| (X1 |*| X2))) ~⚬ (Y1 |*| Y2) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.assocRL_this_ixi")

      override def ix_this_swap[X]: (((A1 |*| A2) |*| X) |*| (A3 |*| A4)) ~⚬ (X |*| (B1 |*| B2)) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_swap")

      override def ix_this_assocLR[X, Y](that: AssocLR[B1, B2, X, Y]): (((A1 |*| A2) |*| X) |*| (A3 |*| A4)) ~⚬ (B1 |*| Y) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ix_this_assocLR($that)")

      override def ix_this_ix[X, Y](that: IX[B1, B2, X, Y]): (((A1 |*| A2) |*| X) |*| (A3 |*| A4)) ~⚬ (Y |*| B2) =
        decompose(IX(g1).asShuffle > that.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(ix > fst(f1), fst(f2), IXI(h, g2))
        }

      override def xi_this_assocRL[X, Y](g: AssocRL[X, B1, B2, Y]): ((A1 |*| A2) |*| (X |*| (A3 |*| A4))) ~⚬ (Y |*| B2) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_assocRL($g)")

      override def xi_this_xi[X, C](
        g: XI[X, B1, B2, C],
      ): ((A1 |*| A2) |*| (X |*| (A3 |*| A4))) ~⚬ (B1 |*| C) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.xi_this_xi($g)")

      override def ixi_fstThis_assocLR[P1, P2, Q, R](
        g2: TransferOpt[P1 |*| P2, Q],
        that: AssocLR[B1, B2, Q, R],
      ): (((A1 |*| A2) |*| P1) |*| ((A3 |*| A4) |*| P2)) ~⚬ (B1 |*| R) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_fstThis_assocLR")

      override def invert: Xfer[B1, B2, _, _, A1 |*| A2, A3 |*| A4] =
        Xfer(g1.asShuffle.invert, g2.asShuffle.invert, IXI(TransferOpt.None(), TransferOpt.None()))

      override def _ixiPairWith_:[X1, X2, X3, X4, Y1, Y2](
        that: Transfer.IXI[X1, X2, X3, X4, Y1, Y2],
      ): BiTransferOpt[X1 |*| X2, X3 |*| X4, A1 |*| A2, A3 |*| A4, Y1 |*| Y2, B1 |*| B2] =
        BiTransferOpt.IXI_IXI(that, this)

      override def _nonePairWith_:[X1, X2](
        that: TransferOpt.None[X1 |*| X2],
      ): BiTransferOpt[X1, X2, A1 |*| A2, A3 |*| A4, X1 |*| X2, B1 |*| B2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.nonePairWith_:($that)")

      override def _swapPairWith_:[X1, X2](that: Transfer.Swap[X1, X2]): BiTransferOpt[X1, X2, A1 |*| A2, A3 |*| A4, X2 |*| X1, B1 |*| B2] =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.swapPairWith_:")

      override def _pairWith[X3, X4, Z](that: TransferOpt[X3 |*| X4, Z]): BiTransferOpt[A1 |*| A2, A3 |*| A4, X3, X4, B1 |*| B2, Z] =
        this ixiPairWith_: that
    }

    def swap_then_assocLR[X1, X2, X3, Y](
      f: Swap[X1, X2 |*| X3],
      g: AssocLR[X2, X3, X1, Y]
    ): (X1 |*| (X2 |*| X3)) ~⚬ (X2 |*| Y) =
      xi(swap > g.g.asShuffle)

    def swap_then_assocRL[X1, X2, X3, Y](
      f: Swap[X1 |*| X2, X3],
      g: AssocRL[X3, X1, X2, Y],
    ): ((X1 |*| X2) |*| X3) ~⚬ (Y |*| X2) =
      ix(swap > g.g.asShuffle)

    def assocLR_then_assocLR[A1, A2, A3, A4, B, C](
      f: AssocLR[A1 |*| A2, A3, A4, B],
      g: AssocLR[A1, A2, B, C],
    ): (((A1 |*| A2)|*| A3) |*| A4) ~⚬ (A1 |*| C) =
      decompose(assocLR > snd(f.g.asShuffle) > g.g.asShuffle) match {
        case Decomposition(f1, f2, g) => Xfer(assocLR > snd(f1), f2, AssocLR(g))
      }

    def assocLR_then_assocRL[A1, A2, A3, B2, B3, C](
      f: AssocLR[A1, A2, A3, B2 |*| B3],
      g: AssocRL[A1, B2, B3, C],
    ): ((A1 |*| A2) |*| A3) ~⚬ (C |*| B3) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          par(snd(i) > g.g.asShuffle, j)
        case Left(t) =>
          t.assocLR_this_assocRL(g)
      }

    def assocLR_then_xi[A1, A2, A3, B2, B3, C](
      f: AssocLR[A1, A2, A3, B2 |*| B3],
      g: XI[A1, B2, B3, C],
    ): ((A1 |*| A2) |*| A3) ~⚬ (B2 |*| C) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          Xfer(snd(i) > swap, j, AssocLR(g.g))
        case Left(t) =>
          t.assocLR_this_xi(g)
      }

    def assocRL_then_assocLR[A1, A2, A3, B1, B2, C](
      f: AssocRL[A1, A2, A3, B1 |*| B2],
      g: AssocLR[B1, B2, A3, C],
    ): (A1 |*| (A2 |*| A3)) ~⚬ (B1 |*| C) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          par(i, fst(j) > g.g.asShuffle)
        case Left(t) =>
          t.assocRL_this_assocLR(g)
      }

    def ix_then_assocRL[A1, A2, A3, A4, B, C](
      f: IX[A1, A2 |*| A3, A4, B],
      g: AssocRL[B, A2, A3, C],
    ): ((A1 |*| (A2 |*| A3)) |*| A4) ~⚬ (C |*| A3) =
      decompose(IX(f.g).asShuffle > g.g.asShuffle) match {
        case Decomposition(f1, f2, h) => Xfer(assocRL > fst(f1), f2, IX(h))
      }

    def xi_then_assocLR[A1, A2, A3, A4, B, C](
      f: XI[A1, A2 |*| A3, A4, B],
      g: AssocLR[A2, A3, B, C],
    ): (A1 |*| ((A2 |*| A3) |*| A4)) ~⚬ (A2 |*| C) =
      decompose(xi > snd(f.g.asShuffle) > g.g.asShuffle) match {
        case Decomposition(f1, f2, g) => Xfer(f1, assocLR > snd(f2), XI(g))
      }

    def xi_then_assocRL[A1, A2, A3, B2, B3, C](
      f: XI[A1, A2, A3, B2 |*| B3],
      g: AssocRL[A2, B2, B3, C],
    ): (A1 |*| (A2 |*| A3)) ~⚬ (C |*| B3) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          decompose(swap > g.g.asShuffle) match {
            case Decomposition(f1, f2, h) => Xfer(i > f1, par(f2, j), AssocRL(h))
          }
        case Left(t) =>
          t.xi_this_assocRL(g)
      }

    def xi_then_xi[A1, A2, A3, B2, B3, C](
      f: XI[A1, A2, A3, B2 |*| B3],
      g: XI[A2, B2, B3, C],
    ): (A1 |*| (A2 |*| A3)) ~⚬ (B2 |*| C) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          par(i, snd(j) > g.g.asShuffle)
        case Left(t) =>
          t.xi_this_xi(g)
      }

  }

  sealed trait BiTransferOpt[A1, A2, A3, A4, B1, B2] {
    import Transfer.{IXI, XI}

    def ixi_this_ixi[B11, B12, B21, B22, C, D](
      h: IXI[B11, B12, B21, B22, C, D],
    )(implicit
      ev1: B1 =:= (B11 |*| B12),
      ev2: B2 =:= (B21 |*| B22),
    ): ((A1 |*| A3) |*| (A2 |*| A4)) ~⚬ (C |*| D)

    def ixi_this_xi[B21, B22, C](
      h: XI[B1, B21, B22, C],
    )(implicit
      ev: B2 =:= (B21 |*| B22),
    ): ((A1 |*| A3) |*| (A2 |*| A4)) ~⚬ (B21 |*| C)
  }

  object BiTransferOpt {
    import Transfer.{AssocRL, IXI, Swap, XI}

    extension[A, B, C, D](ev1: A =:= C) {
      def zip(ev2: B =:= D): (A |*| B) =:= (C |*| D) =
        ev2.substituteCo[[x] =>> (A |*| B) =:= (C |*| x)](
          ev1.substituteCo[[x] =>> (A |*| B) =:= (x |*| B)](
            implicitly[(A |*| B) =:= (A |*| B)]
          )
        )
    }

    case class None_None[A1, A2, A3, A4]() extends BiTransferOpt[A1, A2, A3, A4, A1 |*| A2, A3 |*| A4] {
      override def ixi_this_ixi[B11, B12, B21, B22, C, D](
        h: IXI[B11, B12, B21, B22, C, D],
      )(implicit
        ev1: (A1 |*| A2) =:= (B11 |*| B12),
        ev2: (A3 |*| A4) =:= (B21 |*| B22),
      ): ((A1 |*| A3) |*| (A2 |*| A4)) ~⚬ (C |*| D) = {
        val (a1_eq_b11, a2_eq_b12) = inj.unapply(ev1)
        val (a3_eq_b21, a4_eq_b22) = inj.unapply(ev2)
        val f1: (A1 |*| A3) ~⚬ C = (a1_eq_b11 zip a3_eq_b21).substituteContra[[x] =>> x ~⚬ C](h.g1.asShuffle)
        val f2: (A2 |*| A4) ~⚬ D = (a2_eq_b12 zip a4_eq_b22).substituteContra[[x] =>> x ~⚬ D](h.g2.asShuffle)
        par(f1, f2)
      }

      override def ixi_this_xi[B21, B22, C](
        h: XI[A1 |*| A2, B21, B22, C],
      )(implicit
        ev: (A3 |*| A4) =:= (B21 |*| B22),
      ): ((A1 |*| A3) |*| (A2 |*| A4)) ~⚬ (B21 |*| C) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_this_xi")
    }

    case class Swap_AssocRL[A1, A2, A3, A41, A42, B3](
      swp: Swap[A1, A2],
      arl: AssocRL[A3, A41, A42, B3],
    ) extends BiTransferOpt[A1, A2, A3, A41 |*| A42, A2 |*| A1, B3 |*| A42] {

      override def ixi_this_ixi[B11, B12, B21, B22, C, D](
        h: IXI[B11, B12, B21, B22, C, D],
      )(implicit
        ev1: (A2 |*| A1) =:= (B11 |*| B12),
        ev2: (B3 |*| A42) =:= (B21 |*| B22),
      ): ((A1 |*| A3) |*| (A2 |*| (A41 |*| A42))) ~⚬ (C |*| D) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_this_ixi")

      override def ixi_this_xi[B21, B22, C](
        h: XI[A2 |*| A1, B21, B22, C],
      )(implicit
        ev: (B3 |*| A42) =:= (B21 |*| B22),
      ): ((A1 |*| A3) |*| (A2 |*| (A41 |*| A42))) ~⚬ (B21 |*| C) = {
        val inj(ev1, ev2) = ev
        decompose(assocRL > fst(swap) > h.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(swap > snd(f1), xi > snd(snd(Id0(ev2)) > f2), IXI(ev1.substituteCo(arl.g), h))
        }
      }
    }

    case class IXI_IXI[A1, A2, A3, A4, A5, A6, A7, A8, B1, B2, C1, C2](
      ixi1: IXI[A1, A2, A3, A4, B1, B2],
      ixi2: IXI[A5, A6, A7, A8, C1, C2],
    ) extends BiTransferOpt[(A1 |*| A2), (A3 |*| A4), (A5 |*| A6), (A7 |*| A8), (B1 |*| B2), (C1 |*| C2)] {

      override def ixi_this_ixi[B11, B12, B21, B22, C, D](
        h: IXI[B11, B12, B21, B22, C, D],
      )(implicit
        ev1: (B1 |*| B2) =:= (B11 |*| B12),
        ev2: (C1 |*| C2) =:= (B21 |*| B22),
      ): (((A1 |*| A2) |*| (A5 |*| A6)) |*| ((A3 |*| A4) |*| (A7 |*| A8))) ~⚬ (C |*| D) = {
        val (b1_eq_b11, b2_eq_b12) = inj.unapply(ev1)
        val (c1_eq_b21, c2_eq_b22) = inj.unapply(ev2)

        par(ixi, ixi) > ixi > par(ixi, ixi) > par(
          par(ixi1.g1.asShuffle, ixi2.g1.asShuffle) > (b1_eq_b11 zip c1_eq_b21).substituteContra[[x] =>> x ~⚬ C](h.g1.asShuffle),
          par(ixi1.g2.asShuffle, ixi2.g2.asShuffle) > (b2_eq_b12 zip c2_eq_b22).substituteContra[[x] =>> x ~⚬ D](h.g2.asShuffle),
        )
      }

      override def ixi_this_xi[B21, B22, C](
        h: XI[B1 |*| B2, B21, B22, C],
      )(implicit
        ev: (C1 |*| C2) =:= (B21 |*| B22),
      ): (((A1 |*| A2) |*| (A5 |*| A6)) |*| ((A3 |*| A4) |*| (A7 |*| A8))) ~⚬ (B21 |*| C) =
        UnhandledCase.raise(s"${this.getClass.getSimpleName}.ixi_this_xi")
    }

    def apply[A1, A2, A3, A4, B1, B2](
      t1: TransferOpt[A1 |*| A2, B1],
      t2: TransferOpt[A3 |*| A4, B2],
    ): BiTransferOpt[A1, A2, A3, A4, B1, B2] =
      t1 pairWith t2
  }
}