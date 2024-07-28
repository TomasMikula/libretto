package libretto.scaletto.impl

import libretto.lambda.util.{BiInjective, TypeEq}
import libretto.lambda.util.TypeEq.Refl

// The types defined herein are all "imaginary", never instantiated, but we declare them as classes,
// so that the Scala typechecker can infer that
//  1. they are injective (e.g. that if `(A |*| B) =:= (C |*| D)` then `A =:= C` and `B =:= D`;
//  2. they are all distinct types (e.g. `One` can never be unified with `Done`).
//     Unfortunately, the Scala typechecker doesn't take advantage of this second fact.
object phantoms {
  final class One private()
  final class Void private()
  final class Done private()
  final class Need private()
  final class Ping private()
  final class Pong private()
  final class RTerminus private()
  final class LTerminus private()
  final class |*|[A, B] private()
  final class |+|[A, B] private()
  final class |&|[A, B] private()
  final class ||[A, B] private()
  final class ::[Label, T] private ()
  final class OneOf[Cases] private()
  final class Rec[F[_]] private()
  final class Sub[A, B] private()
  final class -[A] private()
  final class Val[A] private()
  final class Res[A] private()

  given BiInjective[|*|] with {
    override def unapply[A, B, X, Y](ev: (A |*| B) =:= (X |*| Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(Refl()) => (summon, summon) }
  }

  given BiInjective[|+|] with {
    override def unapply[A, B, X, Y](ev: (A |+| B) =:= (X |+| Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(Refl()) => (summon, summon) }
  }

  given BiInjective[||] with {
    override def unapply[A, B, X, Y](ev: (A || B) =:= (X || Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(Refl()) => (summon, summon) }
  }

  given biInjectiveFlippedSeparator: BiInjective[[x, y] =>> y || x] =
    BiInjective[||].flip

  given BiInjective[::] with {
    override def unapply[A, B, X, Y](ev: (A :: B) =:= (X :: Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(Refl()) => (summon, summon) }
  }
}

def bug[A](msg: String): A =
  throw new AssertionError(
    s"""$msg
        |This is a bug, please report at https://github.com/TomasMikula/libretto/issues/new?labels=bug"""
      .stripMargin
  )
