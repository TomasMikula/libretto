package libretto.typology.toylang.terms

import libretto.lambda.util.SourcePos
import libretto.typology.toylang.types.{AbstractTypeLabel, Fix, RecCall, TypeTag}

sealed trait TypedFun[A, B] {
  import TypedFun._

  def inType: Type =
    this match
      case Id(typ)           => typ
      case AndThen(f, tx, g) => f.inType
      case Par(f1, f2)       => Type.pair(f1.inType, f2.inType)
      case EitherF(f1, f2)   => Type.sum(f1.inType, f2.inType)
      case InjectL(ta, tb)   => ta
      case InjectR(ta, tb)   => tb
      case Rec(f)            => ???
      case Recur(ta, tb)     => Type.pair(Type.recCall(ta, tb), ta)
      case FixF(f)           => TypeTag.toType(TypeTag.app(f, TypeTag.fix(using f))).vmap(identity)
      case UnfixF(f)         => TypeTag.toType(TypeTag.fix(using f)).vmap(identity)
      case IntToString       => Type.int

  def outType: Type =
    this match
      case Id(typ)           => typ
      case AndThen(f, tx, g) => g.outType
      case Par(f1, f2)       => Type.pair(f1.outType, f2.outType)
      case EitherF(f1, f2)   => f1.outType
      case InjectL(ta, tb)   => Type.sum(ta, tb)
      case InjectR(ta, tb)   => Type.sum(ta, tb)
      case Rec(f)            => f.outType
      case Recur(ta, tb)     => tb
      case FixF(f)           => TypeTag.toType(TypeTag.fix(using f)).vmap(identity)
      case UnfixF(f)         => TypeTag.toType(TypeTag.app(f, TypeTag.fix(using f))).vmap(identity)
      case IntToString       => Type.string
}

object TypedFun {
  type Type = libretto.typology.toylang.types.Type[AbstractTypeLabel]
  def Type  = libretto.typology.toylang.types.Type

  case class Id[A](typ: Type) extends TypedFun[A, A]
  case class AndThen[A, X, B](f: TypedFun[A, X], tx: Type, g: TypedFun[X, B]) extends TypedFun[A, B]
  case class Par[A1, A2, B1, B2](f1: TypedFun[A1, B1], f2: TypedFun[A2, B2]) extends TypedFun[(A1, A2), (B1, B2)]
  case class AssocLR[A, B, C](ta: Type, tb: Type, tc: Type) extends TypedFun[((A, B), C), (A, (B, C))]
  case class AssocRL[A, B, C](ta: Type, tb: Type, tc: Type) extends TypedFun[(A, (B, C)), ((A, B), C)]
  case class Swap[A, B](ta: Type, tb: Type) extends TypedFun[(A, B), (B, A)]
  case class EitherF[A1, A2, B](f1: TypedFun[A1, B], f2: TypedFun[A2, B]) extends TypedFun[Either[A1, A2], B]
  case class InjectL[A, B](ta: Type, tb: Type) extends TypedFun[A, Either[A, B]]
  case class InjectR[A, B](ta: Type, tb: Type) extends TypedFun[B, Either[A, B]]
  case class Rec[A, B](f: TypedFun[(RecCall[A, B], A), B]) extends TypedFun[A, B]
  case class Recur[A, B](ta: Type, tb: Type) extends TypedFun[(RecCall[A, B], A), B]
  case class FixF[F[_]](f: TypeTag[F]) extends TypedFun[F[Fix[F]], Fix[F]]
  case class UnfixF[F[_]](f: TypeTag[F]) extends TypedFun[Fix[F], F[Fix[F]]]

  case object IntToString extends TypedFun[Int, String]

  def id[A](typ: Type): TypedFun[A, A] = Id(typ)
  def andThen[A, X, B](f: TypedFun[A, X], tx: Type, g: TypedFun[X, B]): TypedFun[A, B] = AndThen(f, tx, g)
  def par[A1, A2, B1, B2](f1: TypedFun[A1, B1], f2: TypedFun[A2, B2]): TypedFun[(A1, A2), (B1, B2)] = Par(f1, f2)
  def assocLR[A, B, C](ta: Type, tb: Type, tc: Type): TypedFun[((A, B), C), (A, (B, C))] = AssocLR(ta, tb, tc)
  def assocRL[A, B, C](ta: Type, tb: Type, tc: Type): TypedFun[(A, (B, C)), ((A, B), C)] = AssocRL(ta, tb, tc)
  def swap[A, B](ta: Type, tb: Type): TypedFun[(A, B), (B, A)] = Swap(ta, tb)
  def either[A1, A2, B](f1: TypedFun[A1, B], f2: TypedFun[A2, B]): TypedFun[Either[A1, A2], B] = EitherF(f1, f2)
  def injectL[A, B](ta: Type, tb: Type): TypedFun[A, Either[A, B]] = InjectL(ta, tb)
  def injectR[A, B](ta: Type, tb: Type): TypedFun[B, Either[A, B]] = InjectR(ta, tb)
  def rec[A, B](f: TypedFun[(RecCall[A, B], A), B]): TypedFun[A, B] = Rec(f)
  def recur[A, B](ta: Type, tb: Type): TypedFun[(RecCall[A, B], A), B] = Recur(ta, tb)
  def fix[F[_]](f: TypeTag[F]): TypedFun[F[Fix[F]], Fix[F]] = FixF(f)
  def unfix[F[_]](f: TypeTag[F]): TypedFun[Fix[F], F[Fix[F]]] = UnfixF(f)

  def intToString: TypedFun[Int, String] = IntToString
}
