package libretto.typology.toylang.terms

import libretto.lambda.SymmetricSemigroupalCategory
import libretto.typology.toylang.types.{Fix, RecCall, TypeTag}

case class Fun[A, B](value: FunT[Fun, A, B]) {
  def >[C](that: Fun[B, C]): Fun[A, C] =
    Fun(FunT.AndThen(this, that))
}

object Fun {
  def id[A]: Fun[A, A] =
    Fun(FunT.IdFun())

  def andThen[A, B, C](f: Fun[A, B], g: Fun[B, C]): Fun[A, C] =
    Fun(FunT.AndThen(f, g))

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

  def rec[A, B](f: Fun[(RecCall[A, B], A), B]): Fun[A, B] =
    Fun(FunT.Rec(f))

  def recFun[A, B](f: LambdaContext ?=> Expr[RecCall[A, B]] => Expr[A] => Expr[B]): Fun[A, B] = {
    val g: Fun[(RecCall[A, B], A), B] =
      fun { case self <*> a => f(self)(a) }
    rec(g)
  }

  def recur[A, B]: Fun[(RecCall[A, B], A), B] =
    Fun(FunT.Recur())

  def constInt(n: Int): Fun[Unit, Int] =
    Fun(FunT.ConstInt(n))

  def addInts: Fun[(Int, Int), Int] =
    Fun(FunT.AddInts())

  def intToString: Fun[Int, String] =
    Fun(FunT.IntToString())

  private given SymmetricSemigroupalCategory[Fun, Tuple2] with {
    override def andThen[A, B, C](f: Fun[A, B], g: Fun[B, C]): Fun[A, C] = Fun.andThen(f, g)
    override def id[A]: Fun[A, A] = Fun.id[A]
    override def par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]): Fun[(A1, A2), (B1, B2)] = Fun.par(f1, f2)
    override def assocLR[A, B, C]: Fun[((A, B), C), (A, (B, C))] = ???
    override def assocRL[A, B, C]: Fun[(A, (B, C)), ((A, B), C)] = ???
    override def swap[A, B]: Fun[(A, B), (B, A)] = ???
  }

  private val lambdas: libretto.lambda.Lambdas[Fun, Tuple2, Object] =
    libretto.lambda.Lambdas[Fun, Tuple2, Object]

  opaque type LambdaContext = lambdas.Context

  opaque type Expr[A] = lambdas.Expr[A]

  def fun[A, B](f: LambdaContext ?=> Expr[A] => Expr[B]): Fun[A, B] = {
    import libretto.lambda.Lambdas
    import Lambdas.Abstracted.{Closure, Exact, Failure}
    import libretto.lambda.Var

    lambdas.absTopLevel(new Object, f) match {
      case Exact(f) =>
        f.fold
      case Closure(captured, f) =>
        val undefinedVars: Var.Set[Object] =
          lambdas.Expr.initialVars(captured)
        throw new IllegalArgumentException(s"Undefined variables: $undefinedVars")
      case Failure(e) =>
        throw new IllegalArgumentException(s"$e")
    }
  }

  extension [A, B](f: Fun[A, B]) {
    def apply(a: Expr[A])(using LambdaContext): Expr[B] =
      lambdas.Expr.map(a, f)(new Object)
  }

  extension [A](a: Expr[A]) {
    def <*>[B](b: Expr[B])(using LambdaContext): Expr[(A, B)] =
      lambdas.Expr.zip(a, b)(new Object)
  }

  extension [A, B](f: Expr[RecCall[A, B]]) {
    def apply(a: Expr[A])(using LambdaContext): Expr[B] =
      Fun.recur(f <*> a)
  }

  object <*> {
    def unapply[A, B](using LambdaContext)(x: Expr[(A, B)]): (Expr[A], Expr[B]) =
      lambdas.Expr.unzip(x)(new Object, new Object)
  }
}
