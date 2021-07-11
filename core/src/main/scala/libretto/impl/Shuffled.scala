package libretto.impl

import libretto.BiInjective

class Shuffled[->[_, _], |*|[_, _]](using BiInjective[|*|]) {
  val shuffle = new Shuffle[|*|]
  import shuffle.{~⚬, TransferOpt}

  sealed trait Shuffled[A, B] {
    def after[Z](that: Shuffled[Z, A]): Shuffled[Z, B]
    def thenShuffle[C](that: B ~⚬ C): Shuffled[A, C]
    def fold(using SymmetricSemigroupalCategory[->, |*|]): A -> B
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

    override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B = {
      val (f, g, h) = (l.fold, m.fold, r.fold)
      ev.andThen(f, ev.andThen(g, h))
    }

    override def inSnd[P]: Shuffled[P |*| A, P |*| B] =
      SemiObstructed(~⚬.snd(l), m, r, TransferOpt.None())
  }

  case class Pure[A, B](s: A ~⚬ B) extends Permeable[A, B] {
    override def after[Z](that: Shuffled[Z, A]): Shuffled[Z, B] =
      that thenShuffle s

    override def thenShuffle[C](t: B ~⚬ C): Pure[A, C] =
      Pure(s > t)

    override def fold(using SymmetricSemigroupalCategory[->, |*|]): A -> B =
      s.fold

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
        case SemiObstructed(_, _, _, _) =>
          ???
      }

    override def thenShuffle[C](s: B ~⚬ C): SemiObstructed[A, _, X2, Y2, _, C] =
      ~⚬.decompose(right.asShuffle > s) match {
        case ~⚬.Decomposition(g1, g2, h) => SemiObstructed(left > ~⚬.fst(g1), bottom1, bottom2 > g2, h)
      }

    override def fold(using ev: SymmetricSemigroupalCategory[->, |*|]): A -> B = {
      val (f, g, h, i) = (left.fold, bottom1.fold, bottom2.fold, right.fold)
      ev.andThen(f, ev.andThen(ev.snd(ev.andThen(g, h)), i))
    }

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
    ???

  def snd[X, Y, Z](f: Shuffled[Y, Z]): Shuffled[X |*| Y, X |*| Z] =
    f.inSnd[X]

  def assocLR[X, Y, Z]: Shuffled[(X |*| Y) |*| Z, X |*| (Y |*| Z)] =
    Pure(~⚬.assocLR)

  def assocRL[X, Y, Z]: Shuffled[X |*| (Y |*| Z), (X |*| Y) |*| Z] =
    Pure(~⚬.assocRL)

  def lift[X, Y](f: X -> Y): Shuffled[X, Y] =
    Impermeable(~⚬.id, Solid(f), ~⚬.id)
}
