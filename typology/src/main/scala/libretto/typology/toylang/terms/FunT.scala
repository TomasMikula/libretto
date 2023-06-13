package libretto.typology.toylang.terms

import libretto.typology.toylang.types.{Fix, RecCall, TypeTag}

sealed trait FunT[->[_, _], A, B]

object FunT {
  case class IdFun[->[_, _], A]() extends FunT[->, A, A]

  case class AndThen[->[_, _], A, B, C](f: A -> B, g: B -> C) extends FunT[->, A, C]

  case class Par[->[_, _], A1, A2, B1, B2](f1: A1 -> B1, f2: A2 -> B2) extends FunT[->, (A1, A2), (B1, B2)]

  case class AssocLR[->[_, _], A, B, C]() extends FunT[->, ((A, B), C), (A, (B, C))]
  case class AssocRL[->[_, _], A, B, C]() extends FunT[->, (A, (B, C)), ((A, B), C)]
  case class Swap[->[_, _], A, B]() extends FunT[->, (A, B), (B, A)]

  case class EitherF[->[_, _], A, B, C](f: A -> C, g: B -> C) extends FunT[->, A Either B, C]
  case class InjectL[->[_, _], A, B]() extends FunT[->, A, A Either B]
  case class InjectR[->[_, _], A, B]() extends FunT[->, B, A Either B]

  case class Distribute[->[_, _], A, B, C]() extends FunT[->, (A, Either[B, C]), Either[(A, B), (A, C)]]

  case class FixF[->[_, _], F[_]](f: TypeTag[F]) extends FunT[->, F[Fix[F]], Fix[F]]
  case class UnfixF[->[_, _], F[_]](f: TypeTag[F]) extends FunT[->, Fix[F], F[Fix[F]]]

  case class Rec[->[_, _], A, B](f: (RecCall[A, B], A) -> B) extends FunT[->, A, B]
  case class Recur[->[_, _], A, B]() extends FunT[->, (RecCall[A, B], A), B]

  case class ConstInt[->[_, _]](n: Int) extends FunT[->, Unit, Int]

  case class AddInts[->[_, _]]() extends FunT[->, (Int, Int), Int]

  case class IntToString[->[_, _]]() extends FunT[->, Int, String]
}
