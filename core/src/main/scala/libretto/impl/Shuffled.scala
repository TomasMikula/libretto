package libretto.impl

import libretto.BiInjective

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

    def >[C](that: Shuffled[B, C]): Shuffled[A, C] =
      that after this
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
  }

  case class SemiObstructed[A, X1, X2, Y2, Z2, B](
    left    : A ~⚬ (X1 |*| X2),
    bottom1 : Plated[X2, Y2],
    bottom2 : Y2 ~⚬ Z2,
    right   : TransferOpt[X1 |*| Z2, B],
  ) extends Permeable[A, B] {
    override def after[Z](that: Shuffled[Z, A]): Shuffled[Z, B] =
      that match {
        case Pure(s) =>
          SemiObstructed(s > left, bottom1, bottom2, right)
        case Impermeable(l, m, r) =>
          ~⚬.decompose((r > left).invert) match {
            case ~⚬.Decomposition(f1, f2, g) =>
              val m1 = Plated.SemiSnoc(m, RevTransferOpt(g), f2.invert, bottom1)
              Impermeable(l, m1, ~⚬.par(f1.invert, bottom2) > right.asShuffle)
          }
        case SemiObstructed(l, b1, b2, r) =>
          ▄░▄(b1, ~⚬.snd(b2) > r.asShuffle > left, bottom1)
            .afterShuffle(l)
            .thenShuffle(~⚬.snd(bottom2) > right.asShuffle)
      }

    override def thenShuffle[C](s: B ~⚬ C): SemiObstructed[A, _, X2, Y2, _, C] =
      ~⚬.decompose(right.asShuffle > s) match {
        case ~⚬.Decomposition(g1, g2, h) => SemiObstructed(left > ~⚬.fst(g1), bottom1, bottom2 > g2, h)
      }

    override def afterShuffle[Z](that: Z ~⚬ A): Shuffled[Z, B] =
      SemiObstructed(that > left, bottom1, bottom2, right)

    override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B = {
      val (f, g, h, i) = (left.fold, bottom1.fold, bottom2.fold, right.fold)
      ev.andThen(f, ev.andThen(ev.snd(ev.andThen(g, h)), i))
    }

    override def inFst[Q]: Shuffled[A |*| Q, B |*| Q] =
      swap > inSnd[Q] > swap

    override def inSnd[P]: Shuffled[P |*| A, P |*| B] =
      ~⚬.decompose[P |*| X1, Y2, P |*| B](~⚬.snd(bottom2) > ~⚬.assocLR > ~⚬.snd(right.asShuffle)) match {
        case ~⚬.Decomposition(f1, f2, h) =>
          SemiObstructed(~⚬.snd(left) > ~⚬.assocRL > ~⚬.fst(f1), bottom1, f2, h)
      }
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

    def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B
  }

  object Plated {
    case class Solid[A, B](f: A -> B) extends Plated[A, B] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B =
        f
    }

    case class Stacked[A1, A2, B1, B2](f1: Plated[A1, B1], f2: Plated[A2, B2]) extends Plated[A1 |*| A2, B1 |*| B2] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> (B1 |*| B2) =
        ev.par(f1.fold, f2.fold)
    }

    case class Sandwich[A, X, Y, B](l: Plated[A, X], m: X ~⚬ Y, r: Plated[Y, B]) extends Plated[A, B] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B =
        ev.andThen(l.fold, ev.andThen(m.fold, r.fold))
    }

    case class SemiCons[A1, A2, X2, Y2, Z, B](
      semiHead: Plated[A2, X2],
      s: X2 ~⚬ Y2,
      t: TransferOpt[A1 |*| Y2, Z],
      tail: Plated[Z, B],
    ) extends Plated[A1 |*| A2, B] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): (A1 |*| A2) -> B =
        ev.andThen(ev.andThen(ev.snd(ev.andThen(semiHead.fold, s.fold)), t.fold), tail.fold)
    }

    case class SemiSnoc[A, X, Y2, Z2, B1, B2](
      init: Plated[A, X],
      t: RevTransferOpt[X, B1 |*| Y2],
      s: Y2 ~⚬ Z2,
      semiLast: Plated[Z2, B2],
    ) extends Plated[A, B1 |*| B2] {
      override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> (B1 |*| B2) =
        ev.andThen(init.fold, ev.andThen(t.fold, ev.snd(ev.andThen(s.fold, semiLast.fold))))
    }

    case class Preshuffled[A, X, B](s: A ~⚬ X, t: Plated[X, B])
  }
  import Plated._

  case class RevTransferOpt[A, B](t: TransferOpt[B, A]) {
    def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B =
      t.asShuffle.invert.fold
  }

  def id[X]: Shuffled[X, X] =
    Permeable.id

  def pure[X, Y](f: X ~⚬ Y): Shuffled[X, Y] =
    Pure(f)

  def fst[X, Y, Z](f: Shuffled[X, Y]): Shuffled[X |*| Z, Y |*| Z] =
    f.inFst[Z]

  def snd[X, Y, Z](f: Shuffled[Y, Z]): Shuffled[X |*| Y, X |*| Z] =
    f.inSnd[X]

  def assocLR[X, Y, Z]: Shuffled[(X |*| Y) |*| Z, X |*| (Y |*| Z)] =
    Pure(~⚬.assocLR)

  def assocRL[X, Y, Z]: Shuffled[X |*| (Y |*| Z), (X |*| Y) |*| Z] =
    Pure(~⚬.assocRL)

  def swap[X, Y]: Shuffled[X |*| Y, Y |*| X] =
    Pure(~⚬.swap)

  def lift[X, Y](f: X -> Y): Shuffled[X, Y] =
    Impermeable(~⚬.id, Solid(f), ~⚬.id)

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

    case class AssocLR[P1, P2, P3, Q2](value: Transfer.AssocLR[P1, P2, P3, Q2]) extends Tr[P1 |*| P2, P3, P1, Q2] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ (P1 |*| P2),
        f2: X2 ~⚬ P3,
        r: Plated[Q2, Z2],
      ): Shuffled[A1 |*| A2, P1 |*| Z2] =
        SemiObstructed(
          ~⚬.fst(f1) > ~⚬.assocLR,
          Plated.SemiCons(l, f2, value.g, r),
          ~⚬.id,
          TransferOpt.None(),
        )

    }

    case class AssocRL[P1, P2, P3, Q1](value: Transfer.AssocRL[P1, P2, P3, Q1]) extends Tr[P1, P2 |*| P3, Q1, P3] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ P1,
        f2: X2 ~⚬ (P2 |*| P3),
        r: Plated[P3, Z2],
      ): Shuffled[A1 |*| A2, Q1 |*| Z2] =
        revDecompose(f2) match {
          case RevDecomposition(t, g1, g2) =>
            SemiObstructed(
              ~⚬.fst(f1),
              Plated.SemiSnoc(l, t, g2, r),
              ~⚬.fst(g1),
              Transfer.AssocRL(value.g),
            )
        }

    }

    case class IX[P1, P2, P3, Q1](value: Transfer.IX[P1, P2, P3, Q1]) extends Tr[P1 |*| P2, P3, Q1, P2] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ (P1 |*| P2),
        f2: X2 ~⚬ P3,
        r: Plated[P2, Z2],
      ): Shuffled[A1 |*| A2, Q1 |*| Z2] =
        ???

    }

    case class XI[P1, P2, P3, Q2](value: Transfer.XI[P1, P2, P3, Q2]) extends Tr[P1, P2 |*| P3, P2, Q2] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ P1,
        f2: X2 ~⚬ (P2 |*| P3),
        r: Plated[Q2, Z2],
      ): Shuffled[A1 |*| A2, P2 |*| Z2] =
        ???

    }

    case class IXI[P1, P2, P3, P4, Q1, Q2](value: Transfer.IXI[P1, P2, P3, P4, Q1, Q2]) extends Tr[P1 |*| P2, P3 |*| P4, Q1, Q2] {

      override def `▄░_this_▄`[A1, A2, X2, Z2](
        l: Plated[A2, X2],
        f1: A1 ~⚬ (P1 |*| P2),
        f2: X2 ~⚬ (P3 |*| P4),
        r: Plated[Q2, Z2],
      ): Shuffled[A1 |*| A2, Q1 |*| Z2] =
        ???

    }

    def apply[P1, P2, Q1, Q2](t: Transfer[P1, P2, Q1, Q2]): Tr[P1, P2, Q1, Q2] =
      t match {
        case t: Transfer.Swap[_, _]            => Swap(t)
        case t: Transfer.AssocLR[_, _, _, _]   => AssocLR(t)
        case t: Transfer.AssocRL[_, _, _, _]   => AssocRL(t)
        case t: Transfer.IX[_, _, _, _]        => IX(t)
        case t: Transfer.XI[_, _, _, _]        => XI(t)
        case t: Transfer.IXI[_, _, _, _, _, _] => IXI(t)
      }

    def revDecompose[X, Z1, Z2](f: X ~⚬ (Z1 |*| Z2)): RevDecomposition[X, _, _, Z1, Z2] =
      ~⚬.decompose(f.invert) match {
        case ~⚬.Decomposition(f1, f2, g) =>
          RevDecomposition(RevTransferOpt(g), f1.invert, f2.invert)
      }

    case class RevDecomposition[X, Y1, Y2, Z1, Z2](
      t: RevTransferOpt[X, Y1 |*| Y2],
      g1: Y1 ~⚬ Z1,
      g2: Y2 ~⚬ Z2,
    )
  }
}