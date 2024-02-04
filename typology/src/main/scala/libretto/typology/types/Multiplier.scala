package libretto.typology.types

import libretto.lambda.{Projection, StrongZippable, Zippable}
import libretto.lambda.util.Exists

sealed trait Multiplier[×[_, _], A, AA] {
  import Multiplier.*

  def apply[F[_]](fa: F[A])(using Zippable[×, F]): F[AA] =
    this match
      case Id()        => fa
      case Dup(m1, m2) => m1(fa) zip m2(fa)

  def project[B](p: Projection[×, AA, B])(
    inputIsAtomic: [x, y] => (A =:= (x × y)) => Nothing,
  ): Multiplier[×, A, B] =
    p match
      case Projection.Id() => this
      case p: Projection.Proper[prod, aa, b] => projectProper(p, inputIsAtomic)

  protected def projectProper[B](
    p: Projection.Proper[×, AA, B],
    inputIsAtomic: [x, y] => (A =:= (x × y)) => Nothing,
  ): Multiplier[×, A, B]
}

object Multiplier {
  case class Id[×[_, _], A]() extends Multiplier[×, A, A] {
    override def projectProper[B](
      p: Projection.Proper[×, A, B],
      inputIsAtomic: [x, y] => (x: A =:= x × y) => Nothing,
    ): Multiplier[×, A, B] =
      p.startsFromPair match
        case Exists.Some(Exists.Some(ev)) => inputIsAtomic(ev)
  }

  case class Dup[×[_, _], A, A1, A2](
    m1: Multiplier[×, A, A1],
    m2: Multiplier[×, A, A2],
  ) extends Multiplier[×, A, A1 × A2] {
    override def projectProper[B](
      p: Projection.Proper[×, A1 × A2, B],
      inputIsAtomic: [x, y] => (x: A =:= x × y) => Nothing,
    ): Multiplier[×, A, B] =
      p match
        case Projection.DiscardFst(p2) => (m2 project p2)(inputIsAtomic)
        case Projection.DiscardSnd(p1) => (m1 project p1)(inputIsAtomic)
        case Projection.Fst(p1)        => Dup((m1 project p1)(inputIsAtomic), m2)
        case Projection.Snd(p2)        => Dup(m1, (m2 project p2)(inputIsAtomic))
        case Projection.Both(p1, p2)   => Dup((m1 project p1)(inputIsAtomic), (m2 project p2)(inputIsAtomic))

  }

  def dup[×[_, _], A]: Multiplier[×, A, A × A] =
    Dup(Id(), Id())

  def strongZippable[×[_, _], A](
    inputIsAtomic: [x, y] => (A =:= (x × y) => Nothing)
  ): StrongZippable[×, Multiplier[×, A, _]] =
    new StrongZippable[×, Multiplier[×, A, _]] {

      override def zip[X, Y](
        x: Multiplier[×, A, X],
        y: Multiplier[×, A, Y],
      ): Multiplier[×, A, X × Y] =
        Dup(x, y)

      override def unzip[X, Y](
        xy: Multiplier[×, A, X × Y],
      ): (Multiplier[×, A, X], Multiplier[×, A, Y]) =
        xy match
          case Id()        => inputIsAtomic(summon[A =:= (X × Y)])
          case Dup(m1, m2) => (m1, m2)
    }
}
