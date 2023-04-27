package libretto.typology.toylang.terms

import libretto.typology.toylang.types.{Fix, TypeTag}

sealed trait Fun[A, B] {
  def >[C](that: Fun[B, C]): Fun[A, C] =
    Fun.AndThen(this, that)
}

object Fun {
  case class IdFun[A]() extends Fun[A, A]

  case class AndThen[A, B, C](f: Fun[A, B], g: Fun[B, C]) extends Fun[A, C]

  case class Par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]) extends Fun[(A1, A2), (B1, B2)]

  case class EitherF[A, B, C](f: Fun[A, C], g: Fun[B, C]) extends Fun[A Either B, C]
  case class InjectL[A, B]() extends Fun[A, A Either B]
  case class InjectR[A, B]() extends Fun[B, A Either B]

  case class FixF[F[_]](f: TypeTag[F]) extends Fun[F[Fix[F]], Fix[F]]
  case class UnfixF[F[_]](f: TypeTag[F]) extends Fun[Fix[F], F[Fix[F]]]

  case class Rec[A, B](label: Label[A, B], f: Fun[A, B]) extends Fun[A, B]
  object Rec {
    def apply[A, B](f: Fun[A, B] => Fun[A, B]): Rec[A, B] = {
      val label = new Label[A, B]
      Rec[A, B](label, f(RecCall(label)))
    }
  }
  case class RecCall[A, B](label: Label[A, B]) extends Fun[A, B]

  case class ConstInt(n: Int) extends Fun[Unit, Int]

  case class AddInts() extends Fun[(Int, Int), Int]

  case class IntToString() extends Fun[Int, String]

  final class Label[A, B] private[Fun]()

  def id[A]: Fun[A, A] =
    IdFun()

  def par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]): Fun[(A1, A2), (B1, B2)] =
    Par(f1, f2)

  def injectL[A, B]: Fun[A, A Either B] =
    InjectL()

  def injectR[A, B]: Fun[B, A Either B] =
    InjectR()

  def either[A, B, C](f: Fun[A, C], g: Fun[B, C]): Fun[A Either B, C] =
    EitherF(f, g)

  def fix[F[_]](using f: TypeTag[F]): Fun[F[Fix[F]], Fix[F]] =
    FixF[F](f)

  def unfix[F[_]](using f: TypeTag[F]): Fun[Fix[F], F[Fix[F]]] =
    UnfixF[F](f)

  def rec[A, B](f: Fun[A, B] => Fun[A, B]): Fun[A, B] =
    Rec(f)

  def constInt(n: Int): Fun[Unit, Int] =
    ConstInt(n)

  def addInts: Fun[(Int, Int), Int] =
    AddInts()

  def intToString: Fun[Int, String] =
    IntToString()
}
