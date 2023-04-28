package libretto.typology.toylang.terms

import libretto.typology.toylang.types.{Fix, TypeTag}

case class Fun[A, B](value: FunT[Fun, A, B]) {
  def >[C](that: Fun[B, C]): Fun[A, C] =
    Fun(FunT.AndThen(this, that))
}

object Fun {
  def id[A]: Fun[A, A] =
    Fun(FunT.IdFun())

  def par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]): Fun[(A1, A2), (B1, B2)] =
    Fun(FunT.Par(f1, f2))

  def injectL[A, B]: Fun[A, A Either B] =
    Fun(FunT.InjectL())

  def injectR[A, B]: Fun[B, A Either B] =
    Fun(FunT.InjectR())

  def either[A, B, C](f: Fun[A, C], g: Fun[B, C]): Fun[A Either B, C] =
    Fun(FunT.EitherF(f, g))

  def fix[F[_]](using f: TypeTag[F]): Fun[F[Fix[F]], Fix[F]] =
    Fun(FunT.FixF[Fun, F](f))

  def unfix[F[_]](using f: TypeTag[F]): Fun[Fix[F], F[Fix[F]]] =
    Fun(FunT.UnfixF[Fun, F](f))

  def rec[A, B](f: Fun[(FunT.RecCall[A, B], A), B]): Fun[A, B] =
    Fun(FunT.Rec(f))

  def constInt(n: Int): Fun[Unit, Int] =
    Fun(FunT.ConstInt(n))

  def addInts: Fun[(Int, Int), Int] =
    Fun(FunT.AddInts())

  def intToString: Fun[Int, String] =
    Fun(FunT.IntToString())
}
