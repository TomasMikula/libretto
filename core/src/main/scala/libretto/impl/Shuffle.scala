package libretto.impl

import libretto.BiInjective

class Shuffle[->[_, _], |*|[_, _]] {
  sealed trait ~⚬[A, B] {
    import ~⚬._

    def >[C](that: B ~⚬ C)(using inj: BiInjective[|*|], ev: Semigroupoid[->]): A ~⚬ C =
      (this, that) match {
        case (f: PureOp[A, B], g: PureOp[B, C]) => PureOp.andThen(f, g)
        case (f: PureOp[A, B], HCompose(g, h, i)) => HCompose(PureOp.andThen(f, g), h, i)
        case (HCompose(f, g, h), i: PureOp[B, C]) => HCompose(f, g, PureOp.andThen(h, i))
        case (HCompose(f, g, h), HCompose(i, j, k)) => HCompose(f, g.append(PureOp.andThen(h, i), j), k)
      }

    def invert: B ~⚬ A

    def lift(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B = {
      import ev.{andThen, id, par}

      this match {
        case Id()               => id
        case Bimap(Par(f1, f2)) => par(f1.lift, f2.lift)
        case Xfer(xfer)         => xfer.lift
        case HCompose(f, g, h)  => andThen(f.lift, andThen(g.lift, h.lift))
      }
    }
  }

  object ~⚬ {
    /** [[PureOp]]s are combinators that do not use a wrapped function (i.e. "impure") at the top level. */
    sealed trait PureOp[X, Y] extends (X ~⚬ Y)

    object PureOp {
      def andThen[X, Y, Z](
        f: PureOp[X, Y],
        g: PureOp[Y, Z],
      )(using
        inj: BiInjective[|*|],
        ev: Semigroupoid[->],
      ): PureOp[X, Z] =
        (f, g) match {
          case (Id(), g) => g
          case (f, Id()) => f
          case (Bimap(Par(f1, f2)), Bimap(Par(g1, g2))) => par0(f1 > g1, f2 > g2)
          case (Bimap(Par(f1, f2)), Xfer(g)) => Xfer(g.afterBi(f1, f2))
          case (Xfer(f), Bimap(Par(g1, g2))) => Xfer(f.thenBi(g1, g2))
          case (Xfer(f), Xfer(g)) => f > g
        }
    }

    case class Id[X]() extends PureOp[X, X] {
      override def invert: X ~⚬ X =
        this
    }

    /** Non-[[Id]] combinators. */
    sealed trait Composed[X, Y] extends (X ~⚬ Y) {
      override def invert: Composed[Y, X] =
        this match {
          case Bimap(p)    => Bimap(p.invert)
          case Xfer(xfer)  => Xfer(xfer.invert)
          // TODO: HCompose
        }
    }

    /** Combinators that compose smaller operators "vertically", i.e. the composite operates on more inputs than any of the constituents. */
    sealed trait VCompose[X, Y] extends Composed[X, Y] with PureOp[X, Y]

    /** Two parallel operations, at least one of which is not [[Id]]. */
    case class Bimap[X1, X2, Y1, Y2](par: Par[X1, X2, Y1, Y2]) extends VCompose[X1 |*| X2, Y1 |*| Y2]

    /** An operator that transfers resources across inputs. */
    case class Xfer[A1, A2, B1, B2](transfer: Transfer[A1, A2, B1, B2]) extends VCompose[A1 |*| A2, B1 |*| B2]

    case class HCompose[A, X, Y, B](
      pre:    PureOp[A, X],
      middle: Interspersed[X, Y],
      post:   PureOp[Y, B],
    ) extends Composed[A, B]

    def swap[X, Y]: (X |*| Y) ~⚬ (Y |*| X) =
      Xfer(Transfer.Swap(Id(), Id()))

    def assocLR[X, Y, Z]: ((X |*| Y) |*| Z) ~⚬ (X |*| (Y |*| Z)) =
      Xfer(Transfer.AssocLR(Id(), Id()))

    def assocRL[X, Y, Z]: (X |*| (Y |*| Z)) ~⚬ ((X |*| Y) |*| Z) =
      Xfer(Transfer.AssocRL(Id(), Id()))

    def par[X1, X2, Y1, Y2](f1: X1 ~⚬ Y1, f2: X2 ~⚬ Y2): (X1 |*| X2) ~⚬ (Y1 |*| Y2) =
      par0(f1, f2)

    private[Shuffle] def par0[X1, X2, Y1, Y2](f1: X1 ~⚬ Y1, f2: X2 ~⚬ Y2): PureOp[X1 |*| X2, Y1 |*| Y2] =
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
      Xfer(Transfer.XI(Id(), Id()))

    def ix[X, Y, Z]: ((X |*| Y) |*| Z) ~⚬ ((X |*| Z) |*| Y) =
      Xfer(Transfer.IX(Id(), Id()))

    def ixi[W, X, Y, Z]: ((W |*| X) |*| (Y |*| Z)) ~⚬ ((W |*| Y) |*| (X |*| Z)) =
      Xfer(Transfer.IXI(Id(), Id(), Id(), Id()))

    def lift[X, Y](f: X -> Y): X ~⚬ Y =
      HCompose(Id(), Interspersed.Single(f), Id())

    def tryUntangle[X1, X2, Y1, Y2](
      f: (X1 |*| X2) ~⚬ (Y1 |*| Y2)
    )(using
      inj: BiInjective[|*|]
    ): Either[Transfer[X1, X2, Y1, Y2], (X1 ~⚬ Y1, X2 ~⚬ Y2)] =
      f match {
        case Id() =>
          val ev: (X1 |*| X2) =:= (Y1 |*| Y2) =
            summon[(X1 |*| X2) =:= (X1 |*| X2)].asInstanceOf
          val inj(ev1, ev2) = ev
          val f1: X1 ~⚬ Y1 = ev1.substituteCo(Id[X1]())
          val f2: X2 ~⚬ Y2 = ev2.substituteCo(Id[X2]())
          Right((f1, f2))
        case Bimap(Par(f1, f2)) =>
          Right((f1, f2))
        case Xfer(xfer) =>
          Left(xfer)
        // TODO: HCompose
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
  }

  object Par {
    def unapply[X1, X2, Y1, Y2](p: Par[X1, X2, Y1, Y2]): (X1 ~⚬ Y1, X2 ~⚬ Y2) =
      p match {
        case Fst(f1) => (f1, Id())
        case Snd(f2) => (Id(), f2)
        case Both(f1, f2) => (f1, f2)
      }
  }

  enum Interspersed[A, B] {
    case Single[A, B](f: A -> B) extends Interspersed[A, B]
    case Multiple[A, X, Y, B](f: Interspersed[A, X], g: VCompose[X, Y], h: Interspersed[Y, B]) extends Interspersed[A, B]

    def append[C, D](f: PureOp[B, C], g: Interspersed[C, D])(using ev: Semigroupoid[->]): Interspersed[A, D] =
      f match {
        case Id() => this ++ g
        case f: VCompose[B, C] => Multiple(this, f, g)
      }

    def ++[C](that: Interspersed[B, C])(using ev: Semigroupoid[->]): Interspersed[A, C] =
      this match {
        case Single(f) => that.precompose(f)
        case Multiple(f, g, h) => Multiple(f, g, h ++ that)
      }

    def precompose[Z](f: Z -> A)(using ev: Semigroupoid[->]): Interspersed[Z, B] =
      this match {
        case Single(g) => Single(ev.andThen(f, g))
        case Multiple(g, h, i) => Multiple(g.precompose(f), h, i)
      }

    def lift(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B =
      this match {
        case Single(f) => f
        case Multiple(f, g, h) => ev.andThen(f.lift, ev.andThen(g.lift, h.lift))
      }
  }

  enum Transfer[A1, A2, B1, B2] {
    case Swap[X1, X2, Y1, Y2](f1: X1 ~⚬ Y1, f2: X2 ~⚬ Y2) extends Transfer[X1, X2, Y2, Y1]
    case AssocLR[A, A1, X, B2, B](f: A ~⚬ (A1 |*| X), g: (X |*| B2) ~⚬ B) extends Transfer[A, B2, A1, B]
    case AssocRL[B, B2, X, A1, A](f: B ~⚬ (X |*| B2), g: (A1 |*| X) ~⚬ A) extends Transfer[A1, B, A, B2]
    case IX[A, B, A1, X, Y](f: A ~⚬ (A1 |*| Y), g: (A1 |*| B) ~⚬ X) extends Transfer[A, B, X, Y]
    case XI[A, B, B2, X, Y](f: B ~⚬ (X |*| B2), g: (A |*| B2) ~⚬ Y) extends Transfer[A, B, X, Y]
    case IXI[A, B, A1, A2, B1, B2, X, Y](
      f1: A ~⚬ (A1 |*| A2),
      f2: B ~⚬ (B1 |*| B2),
      g1: (A1 |*| B1) ~⚬ X,
      g2: (A2 |*| B2) ~⚬ Y,
    ) extends Transfer[A, B, X, Y]

    def invert: Transfer[B1, B2, A1, A2] =
      this match {
        case Swap(f1, f2)        => Swap(f2.invert, f1.invert)
        case AssocLR(f, g)       => AssocRL(g.invert, f.invert)
        case AssocRL(f, g)       => AssocLR(g.invert, f.invert)
        case IX(f, g)            => IX(g.invert, f.invert)
        case XI(f, g)            => XI(g.invert, f.invert)
        case IXI(f1, f2, g1, g2) => IXI(g1.invert, g2.invert, f1.invert, f2.invert)
      }

    def lift(using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> (B1 |*| B2) = {
      import ev._

      extension [X, Y, Z](f: X -> Y) {
        def >(g: Y -> Z): X -> Z =
          andThen(f, g)
      }

      this match {
        case Swap(f1, f2)        => par(f1.lift, f2.lift) > swap
        case AssocLR(f, g)       => par(f.lift, id) > assocLR > par(id, g.lift)
        case AssocRL(f, g)       => par(id, f.lift) > assocRL > par(g.lift, id)
        case IX(f, g)            => par(f.lift, id) > assocLR > par(id, swap) > assocRL > par(g.lift, id)
        case XI(f, g)            => par(id, f.lift) > assocRL > par(swap, id) > assocLR > par(id, g.lift)
        case IXI(f1, f2, g1, g2) => par(f1.lift, f2.lift) > assocLR > par(id, assocRL > par(swap, id) > assocLR) > assocRL > par(g1.lift, g2.lift)
      }
    }

    def afterBi[X1, X2](f1: X1 ~⚬ A1, f2: X2 ~⚬ A2)(using inj: BiInjective[|*|], ev: Semigroupoid[->]): Transfer[X1, X2, B1, B2] =
      this match {
        case Swap(g1, g2)  => Swap(f1 > g1, f2 > g2)
        case AssocLR(g, h) => AssocLR(f1 > g, snd(f2) > h)
        case AssocRL(g, h) => AssocRL(f2 > g, fst(f1) > h)
        case XI(g, h)      => XI(f2 > g, fst(f1) > h)
        // TODO
      }

    def thenBi[C1, C2](g1: B1 ~⚬ C1, g2: B2 ~⚬ C2)(using inj: BiInjective[|*|], ev: Semigroupoid[->]): Transfer[A1, A2, C1, C2] =
      this match {
        case Swap(f1, f2)  => Swap(f1 > g2, f2 > g1)
        case XI(f, g)      => XI(f > fst(g1), g > g2)
        case IX(f, g)      => IX(f > snd(g2), g > g1)
        case AssocLR(f, g) => AssocLR(f > fst(g1), g > g2)
        case AssocRL(f, g) => AssocRL(f > snd(g2), g > g1)
        // TODO
      }

    def >[C1, C2](
      that: Transfer[B1, B2, C1, C2],
    )(using
      inj: BiInjective[|*|],
      ev: Semigroupoid[->],
    ): PureOp[A1 |*| A2, C1 |*| C2] = {
      import ~⚬._

      this match {
        case Swap(f1, f2) =>
          that match {
            case Swap(g1, g2) =>
              par0(f1 > g2, f2 > g1)
            case AssocLR(g, h) =>
              Xfer(XI(f2 > g, fst(f1) > swap > h))
            case AssocRL(g, h) =>
              Xfer(IX(f1 > g, snd(f2) > swap > h))
            // TODO
          }
        case AssocLR(f, g) =>
          that match {
            case Swap(h1, h2) =>
              Xfer(IX(f > fst(h1) > swap, g > h2))
            case AssocLR(h, i) =>
              Xfer(AssocLR(f > fst(h) > assocLR, assocLR > snd(g) > i))
            case AssocRL(h, i) =>
              tryUntangle(g > h) match {
                case Right((g1, g2)) =>
                  par0(f > snd(g1) > i, g2)
                case Left(gh) =>
                  gh match {
                    case Swap(g1, g2) => Xfer(IX(f > snd(g1), snd(g2) > i))
                    case AssocLR(g, h) => Xfer(AssocLR(f > snd(g) > assocRL > fst(i), h))
                    case AssocRL(g, h) => Xfer(AssocRL(g, fst(f) > assocLR > snd(h) > i))
                    // TODO
                  }
              }
            case XI(h, i) =>
              tryUntangle(g > h) match {
                case Right((g1, g2)) =>
                  Xfer(AssocLR(f > swap > fst(g1), snd(g2) > i))
                // TODO
              }
            // TODO
          }
        case AssocRL(f, g) =>
          that match {
            case Swap(h1, h2) =>
              Xfer(XI(f > snd(h2) > swap, g > h1))
            case AssocRL(h, i) =>
              Xfer(AssocRL(f > snd(h) > assocRL, assocRL > fst(g) > i))
            // TODO
          }
        case XI(f, g) =>
          that match {
            case Swap(h1, h2) =>
              Xfer(AssocRL(f > swap > snd(h1), g > h2))
            case AssocLR(h, i) =>
              Xfer(XI(f > fst(h) > assocLR, Xfer(XI(Id(), g)) > i))
            case AssocRL(h, i) =>
              tryUntangle(g > h) match {
                case Right((g1, g2)) =>
                  Xfer(AssocRL(f > snd(g2), fst(g1) > swap > i))
                case Left(gh) =>
                  gh match {
                    case Swap(g1, g2) => Xfer(Swap(g1, f > snd(g2) > i))
                    case AssocRL(g, h) => Xfer(AssocRL(f > snd(g) > assocRL, xi > snd(h) > i))
                    case XI(g, h) => Xfer(XI(f > snd(g) > assocRL > fst(i), h))
                    case IX(g, h) => Xfer(IX(g, snd(f) > xi > snd(h) > i))
                    // TODO
                  }
              }
            case XI(h, i) =>
              tryUntangle(g > h) match {
                case Right((g1, g2)) =>
                  par0(g1, f > snd(g2) > i)
                case Left(gh) =>
                  gh match {
                    case Swap(g1, g2) => Xfer(XI(f > swap > fst(g2), fst(g1) > swap > i))
                    case AssocRL(g, h) => Xfer(AssocRL(f > snd(g) > xi > snd(i), h))
                    case XI(g, h) => Xfer(XI(f > snd(g) > xi, xi > snd(h) > i))
                    // TODO
                  }
              }
            // TODO
          }
        case IX(f, g) =>
          that match {
            case AssocRL(h, i) => Xfer(IX(f > snd(h) > assocRL, ix > fst(g) > i))
          }
        // TODO
      }
    }
  }
}