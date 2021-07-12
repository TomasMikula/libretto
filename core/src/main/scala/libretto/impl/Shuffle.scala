package libretto.impl

import libretto.BiInjective

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
  }

  object ~⚬ {
    sealed trait Id0[A, B] extends (A ~⚬ B) {
      def ev: A =:= B
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

    case class Decomposition[X1, X2, Y1, Y2, Z](f1: X1 ~⚬ Y1, f2: X2 ~⚬ Y2, g: TransferOpt[Y1 |*| Y2, Z])
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

    def asShuffle: A ~⚬ B =
      this match {
        case x: Transfer[_, _, _, _] => Xfer(Id(), Id(), x)
        case TransferOpt.None() => Id()
      }
  }
  object TransferOpt {
    sealed trait None0[A, B] extends TransferOpt[A, B] {
      def ev: A =:= B
    }

    case class None[X]() extends None0[X, X] {
      override def fold[->[_, _]](using ev: SymmetricSemigroupalCategory[->, |*|]): X -> X =
        ev.id

      override def ev: X =:= X =
        summon[X =:= X]
    }

    def decompose[A1, A2, B1, B2](f: TransferOpt[A1 |*| A2, B1 |*| B2]): Either[Transfer[A1, A2, B1, B2], (Id0[A1, B1], Id0[A2, B2])] =
      f match {
        case t: Transfer[A1, A2, B1, B2] =>
          Left(t)
        case n: TransferOpt.None0[A1 |*| A2, B1 |*| B2] =>
          val (ev1, ev2) = inj.unapply(n.ev)
          Right((ev1.substituteCo(Id()), ev2.substituteCo(Id())))
      }
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

    def assocLR_this_assocRL[X, Y](h: AssocRL[X, B1, B2, Y]): ((X |*| A1) |*| A2) ~⚬ (Y |*| B2)

    def assocRL_this_assocLR[X, Y](h: AssocLR[B1, B2, X, Y]): (A1 |*| (A2 |*| X)) ~⚬ (B1 |*| Y)

    def xi_this_assocRL[X, Y](g: AssocRL[X, B1, B2, Y]): (A1 |*| (X |*| A2)) ~⚬ (Y |*| B2)

    def xi_this_xi[X, C](g: XI[X, B1, B2, C]): (A1 |*| (X |*| A2)) ~⚬ (B1 |*| C)

    def invert: Xfer[B1, B2, _, _, A1, A2]

    def >[C1, C2](that: Transfer[B1, B2, C1, C2]): (A1 |*| A2) ~⚬ (C1 |*| C2) =
      that after this

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

      override def thenXI[X11, X12, C](
        that: XI[X2, X11, X12, C],
      )(implicit
        ev: X1 =:= (X11 |*| X12),
      ): (X1 |*| X2) ~⚬ (X11 |*| C) =
        ???

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: X2 =:= (B11 |*| B12),
        ev2: X1 =:= (B21 |*| B22),
      ): (X1 |*| X2) ~⚬ (C |*| D) =
        ???

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, X2, X1, Y]): ((X |*| X1) |*| X2) ~⚬ (Y |*| X1) =
        IX[X, X1, X2, Y](h.g).asShuffle

      override def assocRL_this_assocLR[X, Y](h: AssocLR[X2, X1, X, Y]): (X1 |*| (X2 |*| X)) ~⚬ (X2 |*| Y) =
        XI(h.g).asShuffle

      override def xi_this_assocRL[X, Y](g: AssocRL[X, X2, X1, Y]): (X1 |*| (X |*| X2)) ~⚬ (Y |*| X1) =
        Xfer(Id(), g.g.asShuffle, Swap())

      override def xi_this_xi[X, C](g: XI[X, X2, X1, C]): (X1 |*| (X |*| X2)) ~⚬ (X2 |*| C) =
        decompose(swap > g.g.asShuffle) match {
          case Decomposition(h1, h2, h) => Xfer(h1, fst(h2) > swap, XI(h))
        }

      override def invert: Xfer[X2, X1, _, _, X1, X2] =
        Xfer(Id(), Id(), Swap())
    }

    case class AssocLR[A1, A2, A3, B2](g: TransferOpt[A2 |*| A3, B2]) extends Transfer[A1 |*| A2, A3, A1, B2] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1 |*| A2, A3]): (Z1 |*| Z2) ~⚬ (A1 |*| B2) =
        that thenAssocLR this

      override def thenBi[C1, C2](g1: A1 ~⚬ C1, g2: B2 ~⚬ C2): Xfer[A1 |*| A2, A3, _, _, C1, C2] =
        decompose(g.asShuffle > g2) match {
          case Decomposition(f1, f2, g) => Xfer(par(g1, f1), f2, AssocLR(g))
        }

      override def thenSwap: ((A1 |*| A2) |*| A3) ~⚬ (B2 |*| A1) =
        ???

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

      override def thenXI[B21, B22, C](
        that: XI[A1, B21, B22, C],
      )(implicit
        ev: B2 =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (B21 |*| C) =
        assocLR_then_XI(ev.substituteCo[[x] =>> AssocLR[A1, A2, A3, x]](this), that)

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: A1 =:= (B11 |*| B12),
        ev2: B2 =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (C |*| D) =
        ???

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, A1, B2, Y]): ((X |*| (A1 |*| A2)) |*| A3) ~⚬ (Y |*| B2) =
        Xfer(AssocRL(h.g).asShuffle, Id(), AssocLR(g))

      override def assocRL_this_assocLR[X, Y](h: AssocLR[A1, B2, X, Y]): ((A1 |*| A2) |*| (A3 |*| X)) ~⚬ (A1 |*| Y) =
        ???

      override def xi_this_assocRL[X, Y](g: AssocRL[X, A1, B2, Y]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ (Y |*| B2) =
        ???

      override def xi_this_xi[X, C](g: XI[X, A1, B2, C]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ (A1 |*| C) =
        ???

      override def invert: Xfer[A1, B2, _, _, A1 |*| A2, A3] =
        ???
    }

    case class AssocRL[A1, A2, A3, B](g: TransferOpt[A1 |*| A2, B]) extends Transfer[A1, A2 |*| A3, B, A3] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1, A2 |*| A3]): (Z1 |*| Z2) ~⚬ (B |*| A3) =
        that.thenAssocRL(this)

      override def thenBi[C1, C2](g1: B ~⚬ C1, g2: A3 ~⚬ C2): Xfer[A1, A2 |*| A3, _, _, C1, C2] =
        decompose(g.asShuffle > g1) match {
          case Decomposition(f1, f2, h) => Xfer(f1, par(f2, g2), AssocRL(h))
        }

      override def thenSwap: (A1 |*| (A2 |*| A3)) ~⚬ (A3 |*| B) =
        ???

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
        ???

      override def thenXI[A31, A32, C](
        that: XI[B, A31, A32, C],
      )(implicit
        ev: A3 =:= (A31 |*| A32),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (A31 |*| C) =
        ???

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: B =:= (B11 |*| B12),
        ev2: A3 =:= (B21 |*| B22),
      ): (A1 |*| (A2 |*| A3)) ~⚬ (C |*| D) =
        ???

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, B, A3, Y]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ (Y |*| A3) =
        ???

      override def assocRL_this_assocLR[X, Y](h: AssocLR[B, A3, X, Y]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ (B |*| Y) =
        ???

      override def xi_this_assocRL[X, Y](h: AssocRL[X, B, A3, Y]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ (Y |*| A3) =
        decompose(XI(g).asShuffle > h.g.asShuffle) match {
          case Decomposition(h1, h2, h) => Xfer(h1, assocRL > fst(h2), AssocRL(h))
        }

      override def xi_this_xi[X, C](h: XI[X, B, A3, C]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ (B |*| C) =
        Xfer(Id(), XI(h.g).asShuffle, AssocRL(g))

      override def invert: Xfer[B, A3, _, _, A1, A2 |*| A3] =
        ???
    }

    case class IX[A1, A2, A3, B](g: TransferOpt[A1 |*| A3, B]) extends Transfer[A1 |*| A2, A3, B, A2] {
      override def after[Z1, Z2](that: Transfer[Z1, Z2, A1 |*| A2, A3]): (Z1 |*| Z2) ~⚬ (B |*| A2) =
        ???

      override def thenBi[C1, C2](g1: B ~⚬ C1, g2: A2 ~⚬ C2): Xfer[A1 |*| A2, A3, _, _, C1, C2] =
        decompose(g.asShuffle > g1) match {
          case Decomposition(f1, f2, h) => Xfer(par(f1, g2), f2, IX(h))
        }

      override def thenSwap: ((A1 |*| A2) |*| A3) ~⚬ (A2 |*| B) =
        ???

      override def thenAssocLR[D1, D2, C2](
        that: AssocLR[D1, D2, A2, C2],
      )(implicit
        ev: B =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| A3) ~⚬ (D1 |*| C2) =
        ???

      override def thenAssocRL[X1, X2, C](
        that: AssocRL[B, X1, X2, C],
      )(using
        ev: A2 =:= (X1 |*| X2),
      ): ((A1 |*| A2) |*| A3) ~⚬ (C |*| X2) = {
        val res = ix_then_assocRL(ev.substituteCo[[x] =>> IX[A1, x, A3, B]](this), that)
        ev.substituteContra[[x] =>> ((A1 |*| x) |*| A3) ~⚬ (C |*| X2)](res)
      }

      override def thenXI[A21, A22, C](
        that: XI[B, A21, A22, C],
      )(implicit
        ev: A2 =:= (A21 |*| A22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (A21 |*| C) =
        ???

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: B =:= (B11 |*| B12),
        ev2: A2 =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| A3) ~⚬ (C |*| D) =
        ???

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, B, A2, Y]): ((X |*| (A1 |*| A2)) |*| A3) ~⚬ (Y |*| A2) =
        ???

      override def assocRL_this_assocLR[X, Y](h: AssocLR[B, A2, X, Y]): ((A1 |*| A2) |*| (A3 |*| X)) ~⚬ (B |*| Y) =
        IXI[A1, A2, A3, X, B, Y](g, h.g).asShuffle

      override def xi_this_assocRL[X, Y](h: AssocRL[X, B, A2, Y]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ (Y |*| A2) =
        ix(XI(g).asShuffle > h.g.asShuffle)

      override def xi_this_xi[X, C](h: XI[X, B, A2, C]): ((A1 |*| A2) |*| (X |*| A3)) ~⚬ (B |*| C) =
        ???

      override def invert: Xfer[B, A2, _, _, A1 |*| A2, A3] =
        ???
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
        ???

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, A2, B2, Y]): ((X |*| A1) |*| (A2 |*| A3)) ~⚬ (Y |*| B2) =
        IXI(h.g, g).asShuffle

      override def assocRL_this_assocLR[X, Y](h: AssocLR[A2, B2, X, Y]): (A1 |*| ((A2 |*| A3) |*| X)) ~⚬ (A2 |*| Y) =
        ???

      override def xi_this_assocRL[X, Y](h: AssocRL[X, A2, B2, Y]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ (Y |*| B2) =
        Xfer(Id(), AssocRL(h.g).asShuffle, XI(g))

      override def xi_this_xi[X, C](g: XI[X, A2, B2, C]): (A1 |*| (X |*| (A2 |*| A3))) ~⚬ (A2 |*| C) =
        decompose(xi(this.g.asShuffle) > g.g.asShuffle) match {
          case Decomposition(f1, f2, h) => Xfer(f1, xi(f2), XI(h))
        }

      override def invert: Xfer[A2, B2, _, _, A1, A2 |*| A3] =
        ???
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
        ???

      override def thenAssocLR[D1, D2, C2](
        that: AssocLR[D1, D2, B2, C2],
      )(implicit
        ev: B1 =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (D1 |*| C2) =
        ???

      override def thenAssocRL[D1, D2, C](
        that: AssocRL[B1, D1, D2, C],
      )(using
        ev: B2 =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (C |*| D2) =
        ???

      override def thenXI[D1, D2, C](
        that: XI[B1, D1, D2, C],
      )(implicit
        ev: B2 =:= (D1 |*| D2),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (D1 |*| C) =
        ???

      override def thenIXI[B11, B12, B21, B22, C, D](
        that: IXI[B11, B12, B21, B22, C, D]
      )(implicit
        ev1: B1 =:= (B11 |*| B12),
        ev2: B2 =:= (B21 |*| B22),
      ): ((A1 |*| A2) |*| (A3 |*| A4)) ~⚬ (C |*| D) =
        ???

      override def assocLR_this_assocRL[X, Y](h: AssocRL[X, B1, B2, Y]): ((X |*| (A1 |*| A2)) |*| (A3 |*| A4)) ~⚬ (Y |*| B2) =
        ???

      override def assocRL_this_assocLR[X, Y](h: AssocLR[B1, B2, X, Y]): ((A1 |*| A2) |*| ((A3 |*| A4) |*| X)) ~⚬ (B1 |*| Y) =
        ???

      override def xi_this_assocRL[X, Y](g: AssocRL[X, B1, B2, Y]): ((A1 |*| A2) |*| (X |*| (A3 |*| A4))) ~⚬ (Y |*| B2) =
        ???

      override def xi_this_xi[X, C](
        g: XI[X, B1, B2, C],
      ): ((A1 |*| A2) |*| (X |*| (A3 |*| A4))) ~⚬ (B1 |*| C) =
        ???

      override def invert: Xfer[B1, B2, _, _, A1 |*| A2, A3 |*| A4] =
        Xfer(g1.asShuffle.invert, g2.asShuffle.invert, IXI(TransferOpt.None(), TransferOpt.None()))
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

    def assocLR_then_XI[A1, A2, A3, B2, B3, C](
      f: AssocLR[A1, A2, A3, B2 |*| B3],
      g: XI[A1, B2, B3, C],
    ): ((A1 |*| A2) |*| A3) ~⚬ (B2 |*| C) =
      TransferOpt.decompose(f.g) match {
        case Right((i, j)) =>
          Xfer(snd(i) > swap, j, AssocLR(g.g))
        case Left(t) =>
          ???
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
}