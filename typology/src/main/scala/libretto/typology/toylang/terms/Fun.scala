package libretto.typology.toylang.terms

import libretto.lambda.{CapturingFun, Sink, SymmetricSemigroupalCategory, Tupled}
import libretto.lambda.util.SourcePos
import libretto.lambda.util.Validated.{Invalid, Valid}
import libretto.typology.toylang.types.{Fix, RecCall, TypeTag}

sealed trait Fun[A, B] {
  def >[C](that: Fun[B, C]): Fun[A, C] =
    Fun.AndThen(this, that)
}

object Fun {
  case class IdFun[A]() extends Fun[A, A]

  case class AndThen[A, B, C](f: Fun[A, B], g: Fun[B, C]) extends Fun[A, C]

  case class Par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]) extends Fun[(A1, A2), (B1, B2)]

  case class AssocLR[A, B, C]() extends Fun[((A, B), C), (A, (B, C))]
  case class AssocRL[A, B, C]() extends Fun[(A, (B, C)), ((A, B), C)]
  case class Swap[A, B]() extends Fun[(A, B), (B, A)]

  case class EitherF[A, B, C](f: Fun[A, C], g: Fun[B, C]) extends Fun[A Either B, C]
  case class InjectL[A, B]() extends Fun[A, A Either B]
  case class InjectR[A, B]() extends Fun[B, A Either B]

  case class Distribute[A, B, C]() extends Fun[(A, Either[B, C]), Either[(A, B), (A, C)]]

  case class Dup[A]() extends Fun[A, (A, A)]
  case class Prj1[A, B]() extends Fun[(A, B), A]
  case class Prj2[A, B]() extends Fun[(A, B), B]

  case class FixF[F[_]](f: TypeTag[F]) extends Fun[F[Fix[F]], Fix[F]]
  case class UnfixF[F[_]](f: TypeTag[F]) extends Fun[Fix[F], F[Fix[F]]]

  case class Rec[A, B](f: Fun[(RecCall[A, B], A), B]) extends Fun[A, B]
  case class Recur[A, B]() extends Fun[(RecCall[A, B], A), B]

  case class ConstInt(n: Int) extends Fun[Unit, Int]

  case class AddInts() extends Fun[(Int, Int), Int]

  case class IntToString() extends Fun[Int, String]

  def id[A]: Fun[A, A] =
    IdFun()

  def andThen[A, B, C](f: Fun[A, B], g: Fun[B, C]): Fun[A, C] =
    AndThen(f, g)

  def par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]): Fun[(A1, A2), (B1, B2)] =
    Par(f1, f2)

  def fst[A1, A2, B1](f1: Fun[A1, B1]): Fun[(A1, A2), (B1, A2)] =
    par(f1, id)

  def snd[A1, A2, B2](f2: Fun[A2, B2]): Fun[(A1, A2), (A1, B2)] =
    par(id, f2)

  def assocLR[A, B, C]: Fun[((A, B), C), (A, (B, C))] =
    AssocLR()

  def assocRL[A, B, C]: Fun[(A, (B, C)), ((A, B), C)] =
    AssocRL()

  def swap[A, B]: Fun[(A, B), (B, A)] =
    Swap()

  def injectL[A, B]: Fun[A, A Either B] =
    InjectL()

  def injectR[A, B]: Fun[B, A Either B] =
    InjectR()

  def either[A, B, C](f: Fun[A, C], g: Fun[B, C]): Fun[A Either B, C] =
    EitherF(f, g)

  def distributeL[A, B, C]: Fun[(A, Either[B, C]), Either[(A, B), (A, C)]] =
    Distribute()

  def dup[A]: Fun[A, (A, A)] =
    Dup()

  def prj1[A, B]: Fun[(A, B), A] =
    Prj1()

  def prj2[A, B]: Fun[(A, B), B] =
    Prj2()

  def fix[F[_]](using f: TypeTag[F]): Fun[F[Fix[F]], Fix[F]] =
    FixF[F](f)

  def unfix[F[_]](using f: TypeTag[F]): Fun[Fix[F], F[Fix[F]]] =
    UnfixF[F](f)

  def rec[A, B](f: Fun[(RecCall[A, B], A), B]): Fun[A, B] =
    Rec(f)

  def recFun[A, B](f: LambdaContext ?=> Expr[RecCall[A, B]] => Expr[A] => Expr[B]): Fun[A, B] = {
    val g: Fun[(RecCall[A, B], A), B] =
      fun { case self <*> a => f(self)(a) }
    rec(g)
  }

  def recur[A, B]: Fun[(RecCall[A, B], A), B] =
    Recur()

  def constInt(n: Int): Fun[Unit, Int] =
    ConstInt(n)

  def addInts: Fun[(Int, Int), Int] =
    AddInts()

  def intToString: Fun[Int, String] =
    IntToString()

  private given SymmetricSemigroupalCategory[Fun, Tuple2] with {
    override def andThen[A, B, C](f: Fun[A, B], g: Fun[B, C]): Fun[A, C] = Fun.andThen(f, g)
    override def id[A]: Fun[A, A] = Fun.id[A]
    override def par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]): Fun[(A1, A2), (B1, B2)] = Fun.par(f1, f2)
    override def assocLR[A, B, C]: Fun[((A, B), C), (A, (B, C))] = Fun.assocLR
    override def assocRL[A, B, C]: Fun[(A, (B, C)), ((A, B), C)] = Fun.assocRL
    override def swap[A, B]: Fun[(A, B), (B, A)] = Fun.swap
  }

  private val lambdas: libretto.lambda.Lambdas[Fun, Tuple2, Object, Unit] =
    libretto.lambda.Lambdas[Fun, Tuple2, Object, Unit](
      universalSplit = Some([x] => (_: Unit) => Fun.dup[x]),
      universalDiscard = Some([x, y] => (_: Unit) => Fun.prj2[x, y]),
    )

  opaque type LambdaContext = lambdas.Context

  opaque type Expr[A] = lambdas.Expr[A]

  def fun[A, B](f: LambdaContext ?=> Expr[A] => Expr[B]): Fun[A, B] = {
    import CapturingFun.{Closure, NoCapture}
    import libretto.lambda.Var

    lambdas.delambdifyTopLevel((), new Object, f) match {
      case Valid(NoCapture(f)) =>
        f
      case Valid(Closure(captured, f)) =>
        val undefinedVars: Var.Set[Object] =
          lambdas.Expr.initialVars(captured)
        throw new IllegalArgumentException(s"Undefined variables: $undefinedVars")
      case Invalid(es) =>
        throw new IllegalArgumentException(s"$es")
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

  extension [A, B](x: Expr[Either[A, B]]) {
    def switch[R](f: Either[Expr[A], Expr[B]] => Expr[R])(using LambdaContext): Expr[R] = {
      import CapturingFun.{Closure, NoCapture}

      val fa: lambdas.Delambdified[A, R] = lambdas.delambdifyNested((), new Object, (a: Expr[A]) => f(Left(a)))
      val fb: lambdas.Delambdified[B, R] = lambdas.delambdifyNested((), new Object, (b: Expr[B]) => f(Right(b)))

      (fa zip fb)
        .flatMap { case (fa, fb) =>
          lambdas.switch[Either, Either[A, B], R](
            Sink(fa) <+> Sink(fb),
            [x, y] => (fx: Fun[x, R], fy: Fun[y, R]) => Fun.either(fx, fy),
            [x, y, z] => (_: Unit) => Fun.distributeL[x, y, z],
          )
        }
        .map {
          case NoCapture(f) => f(x)
          case Closure(captured, f) => f(lambdas.Expr.zipN(Tupled.zip(captured, Tupled.atom(x)))(new Object))
        }
        .valueOr { es => throw IllegalArgumentException(s"$es") }
    }
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
