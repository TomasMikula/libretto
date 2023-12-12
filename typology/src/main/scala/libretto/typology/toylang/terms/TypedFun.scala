package libretto.typology.toylang.terms

import libretto.lambda.util.SourcePos
import libretto.typology.kinds.*
import libretto.typology.toylang.types.{AbstractTypeLabel, Fix, RecCall, ScalaTypeParam, TypeTag}

sealed trait TypedFun[A, B] {
  import TypedFun._

  def inType: Type =
    this match
      case Id(typ)             => typ
      case AndThen(f, tx, g)   => f.inType
      case Par(f1, f2)         => Type.pair(f1.inType, f2.inType)
      case AssocLR(ta, tb, tc) => Type.pair(Type.pair(ta, tb), tc)
      case AssocRL(ta, tb, tc) => Type.pair(ta, Type.pair(tb, tc))
      case Swap(ta, tb)        => Type.pair(ta, tb)
      case EitherF(f1, f2)     => Type.sum(f1.inType, f2.inType)
      case InjectL(ta, tb)     => ta
      case InjectR(ta, tb)     => tb
      case Rec(ta, f)          => ta
      case Recur(ta, tb)       => Type.pair(Type.recCall(ta, tb), ta)
      case FixF(f)             => f(Type.fix(f))
      case UnfixF(f)           => Type.fix(f)
      case IntToString         => Type.int
      case AddInts             => Type.pair(Type.int, Type.int)

  def outType: Type =
    this match
      case Id(typ)             => typ
      case AndThen(f, tx, g)   => g.outType
      case Par(f1, f2)         => Type.pair(f1.outType, f2.outType)
      case AssocLR(ta, tb, tc) => Type.pair(ta, Type.pair(tb, tc))
      case AssocRL(ta, tb, tc) => Type.pair(Type.pair(ta, tb), tc)
      case Swap(ta, tb)        => Type.pair(tb, ta)
      case EitherF(f1, f2)     => f1.outType
      case InjectL(ta, tb)     => Type.sum(ta, tb)
      case InjectR(ta, tb)     => Type.sum(ta, tb)
      case Rec(ta, f)          => f.outType
      case Recur(ta, tb)       => tb
      case FixF(f)             => Type.fix(f)
      case UnfixF(f)           => f(Type.fix(f))
      case IntToString         => Type.string
      case AddInts             => Type.int
}

object TypedFun {
  type Label = Either[ScalaTypeParam, AbstractTypeLabel]

  type Type = libretto.typology.toylang.types.Type[Label]
  def  Type = libretto.typology.toylang.types.Type
  type TypeFun[K, L] = libretto.typology.toylang.types.TypeFun[Label, K, L]
  def  TypeFun       = libretto.typology.toylang.types.TypeFun

  case class Id[A](typ: Type) extends TypedFun[A, A]
  case class AndThen[A, X, B](f: TypedFun[A, X], tx: Type, g: TypedFun[X, B]) extends TypedFun[A, B]
  case class Par[A1, A2, B1, B2](f1: TypedFun[A1, B1], f2: TypedFun[A2, B2]) extends TypedFun[(A1, A2), (B1, B2)]
  case class AssocLR[A, B, C](ta: Type, tb: Type, tc: Type) extends TypedFun[((A, B), C), (A, (B, C))]
  case class AssocRL[A, B, C](ta: Type, tb: Type, tc: Type) extends TypedFun[(A, (B, C)), ((A, B), C)]
  case class Swap[A, B](ta: Type, tb: Type) extends TypedFun[(A, B), (B, A)]
  case class EitherF[A1, A2, B](f1: TypedFun[A1, B], f2: TypedFun[A2, B]) extends TypedFun[Either[A1, A2], B]
  case class InjectL[A, B](ta: Type, tb: Type) extends TypedFun[A, Either[A, B]]
  case class InjectR[A, B](ta: Type, tb: Type) extends TypedFun[B, Either[A, B]]
  case class Distribute[A, B, C](ta: Type, tb: Type, tc: Type) extends TypedFun[(A, Either[B, C]), Either[(A, B), (A, C)]]
  case class Prj1[A, B](ta: Type, tb: Type) extends TypedFun[(A, B), A]
  case class Prj2[A, B](ta: Type, tb: Type) extends TypedFun[(A, B), B]
  case class Rec[A, B](ta: Type, f: TypedFun[(RecCall[A, B], A), B]) extends TypedFun[A, B]
  case class Recur[A, B](ta: Type, tb: Type) extends TypedFun[(RecCall[A, B], A), B]
  case class FixF[F[_]](f: TypeFun[●, ●]) extends TypedFun[F[Fix[F]], Fix[F]]
  case class UnfixF[F[_]](f: TypeFun[●, ●]) extends TypedFun[Fix[F], F[Fix[F]]]

  case object IntToString extends TypedFun[Int, String]
  case object AddInts extends TypedFun[(Int, Int), Int]

  def id[A](typ: Type): TypedFun[A, A] = Id(typ)
  def andThen[A, X, B](f: TypedFun[A, X], tx: Type, g: TypedFun[X, B]): TypedFun[A, B] = AndThen(f, tx, g)
  def par[A1, A2, B1, B2](f1: TypedFun[A1, B1], f2: TypedFun[A2, B2]): TypedFun[(A1, A2), (B1, B2)] = Par(f1, f2)
  def assocLR[A, B, C](ta: Type, tb: Type, tc: Type): TypedFun[((A, B), C), (A, (B, C))] = AssocLR(ta, tb, tc)
  def assocRL[A, B, C](ta: Type, tb: Type, tc: Type): TypedFun[(A, (B, C)), ((A, B), C)] = AssocRL(ta, tb, tc)
  def swap[A, B](ta: Type, tb: Type): TypedFun[(A, B), (B, A)] = Swap(ta, tb)
  def either[A1, A2, B](f1: TypedFun[A1, B], f2: TypedFun[A2, B]): TypedFun[Either[A1, A2], B] = EitherF(f1, f2)
  def injectL[A, B](ta: Type, tb: Type): TypedFun[A, Either[A, B]] = InjectL(ta, tb)
  def injectR[A, B](ta: Type, tb: Type): TypedFun[B, Either[A, B]] = InjectR(ta, tb)
  def distribute[A, B, C](ta: Type, tb: Type, tc: Type): TypedFun[(A, Either[B, C]), Either[(A, B), (A, C)]] = Distribute(ta, tb, tc)
  def prj1[A, B](ta: Type, tb: Type): TypedFun[(A, B), A] = Prj1(ta, tb)
  def prj2[A, B](ta: Type, tb: Type): TypedFun[(A, B), B] = Prj2(ta, tb)
  def rec[A, B](ta: Type, f: TypedFun[(RecCall[A, B], A), B]): TypedFun[A, B] = Rec(ta, f)
  def recur[A, B](ta: Type, tb: Type): TypedFun[(RecCall[A, B], A), B] = Recur(ta, tb)
  def fix[F[_]](f: TypeFun[●, ●]): TypedFun[F[Fix[F]], Fix[F]] = FixF(f)
  def unfix[F[_]](f: TypeFun[●, ●]): TypedFun[Fix[F], F[Fix[F]]] = UnfixF(f)

  def intToString: TypedFun[Int, String] = IntToString
  def addInts: TypedFun[(Int, Int), Int] = AddInts
}
