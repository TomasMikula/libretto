package libretto.lambda

import libretto.lambda.Lambdas.Error.LinearityViolation.{OverUnder, Overused, Underused}
import libretto.lambda.util.{BiInjective, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl

sealed trait Fun[A, B] {

}

object Fun {
  final class **[A, B] private()
  final class ++[A, B] private()
  final class Val[A] private()
  type One = Val[Unit]

  case class Id[A]() extends Fun[A, A]
  case class AndThen[A, B, C](f: Fun[A, B], g: Fun[B, C]) extends Fun[A, C]
  case class AssocLR[A, B, C]() extends Fun[(A ** B) ** C, A ** (B ** C)]
  case class AssocRL[A, B, C]() extends Fun[A ** (B ** C), (A ** B) ** C]
  case class Par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]) extends Fun[A1 ** A2, B1 ** B2]
  case class Swap[A, B]() extends Fun[A ** B, B ** A]
  case class IntroFst[A]() extends Fun[A, One ** A]
  case class IntroSnd[A]() extends Fun[A, A ** One]
  case class Prj1[A, B]() extends Fun[A ** B, A]
  case class Prj2[A, B]() extends Fun[A ** B, B]
  case class Dup[A]() extends Fun[A, A ** A]
  case class HandleEither[A, B, C](f: Fun[A, C], g: Fun[B, C]) extends Fun[A ++ B, C]
  case class DistributeL[X, A, B]() extends Fun[X ** (A ++ B), (X ** A) ++ (X ** B)]
  case class MapVal[A, B](f: A => B) extends Fun[Val[A], Val[B]]
  case class LiftPair[A, B]() extends Fun[Val[(A, B)], Val[A] ** Val[B]]
  case class UnliftPair[A, B]() extends Fun[Val[A] ** Val[B], Val[(A, B)]]

  def id[A]: Fun[A, A] = Id()
  def andThen[A, B, C](f: Fun[A, B], g: Fun[B, C]): Fun[A, C] = AndThen(f, g)
  def assocLR[A, B, C]: Fun[(A ** B) ** C, A ** (B ** C)] = AssocLR()
  def assocRL[A, B, C]: Fun[A ** (B ** C), (A ** B) ** C] = AssocRL()
  def par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]): Fun[A1 ** A2, B1 ** B2] = Par(f1, f2)
  def swap[A, B]: Fun[A ** B, B ** A] = Swap()
  def introFst[A]: Fun[A, One ** A] = IntroFst()
  def introSnd[A]: Fun[A, A ** One] = IntroSnd()
  def elimFst[A]: Fun[One ** A, A] = Prj2()
  def elimSnd[A]: Fun[A ** One, A] = Prj1()
  def prj1[A, B]: Fun[A ** B, A] = Prj1()
  def prj2[A, B]: Fun[A ** B, B] = Prj2()
  def dup[A]: Fun[A, A ** A] = Dup()
  def either[A, B, C](f: Fun[A, C], g: Fun[B, C]): Fun[A ++ B, C] = HandleEither(f, g)
  def distributeL[X, A, B]: Fun[X ** (A ++ B), (X ** A) ++ (X ** B)] = DistributeL()
  def mapVal[A, B](f: A => B): Fun[Val[A], Val[B]] = MapVal(f)
  def constVal[A](a: A): Fun[One, Val[A]] = mapVal(_ => a)
  def neglect[A]: Fun[Val[A], One] = mapVal(_ => ())
  def liftPair[A, B]: Fun[Val[(A, B)], Val[A] ** Val[B]] = LiftPair()
  def unliftPair[A, B]: Fun[Val[A] ** Val[B], Val[(A, B)]] = UnliftPair()

  given SymmetricSemigroupalCategory[Fun, **] with {
    override def id[A]: Fun[A, A] = Fun.id[A]
    override def andThen[A, B, C](f: Fun[A, B], g: Fun[B, C]): Fun[A, C] = Fun.andThen(f, g)
    override def assocLR[A, B, C]: Fun[(A ** B) ** C, A ** (B ** C)] = Fun.assocLR
    override def assocRL[A, B, C]: Fun[A ** (B ** C), (A ** B) ** C] = Fun.assocRL
    override def par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]): Fun[A1 ** A2, B1 ** B2] = Fun.par(f1, f2)
    override def swap[A, B]: Fun[A ** B, B ** A] = Fun.swap
  }

  private case class VarDesc(desc: String, pos: Option[SourcePos])
  private object VarDesc {
    def apply(desc: String, pos: SourcePos): VarDesc =
      VarDesc(desc, Some(pos))

    def apply(desc: String): VarDesc =
      VarDesc(desc, None)
  }

  private val lambdas: Lambdas[Fun, **, VarDesc] =
    Lambdas[Fun, **, VarDesc](
      (x, y) => VarDesc(s"auxiliary pairing of ($x, $y)"),
    )

  opaque type $[A] = lambdas.Expr[A]
  opaque type LambdaContext = lambdas.Context

  def one(using pos: SourcePos, ctx: LambdaContext): $[One] =
    lambdas.Expr.const[One](
      introduce = [X] => (_: Unit) => introFst[X],
    )(VarDesc("unit", pos))

  object ** {
    given BiInjective[**] with {
      override def unapply[A, B, X, Y](ev: (A ** B) =:= (X ** Y)): (A =:= X, B =:= Y) =
        ev match { case TypeEq(Refl()) => (summon, summon) }
    }

    def unapply[A, B](ab: $[A ** B])(using pos: SourcePos, ctx: LambdaContext): ($[A], $[B]) = {
      val v1 = VarDesc("The first half of untupling", pos)
      val v2 = VarDesc("The second half of untupling", pos)
      lambdas.Expr.unzip(ab)(v1, v2)
    }
  }

  extension [A](a: $[A]) {
    def **[B](b: $[B])(using pos: SourcePos, ctx: LambdaContext): $[A ** B] =
      lambdas.Expr.zip(a, b)(VarDesc("Pair", pos))

    def >[B](f: Fun[A, B])(using pos: SourcePos, ctx: LambdaContext): $[B] =
      lambdas.Expr.map(a, f)(VarDesc("The result of function application", pos))
  }

  extension [A](a: $[Val[A]]) {
    def *[B](b: $[Val[B]])(using pos: SourcePos, ctx: LambdaContext): $[Val[(A, B)]] =
      (a ** b) > unliftPair
  }

  extension [A, B](ab: $[A ++ B]) {
    def switch[C](f: LambdaContext ?=> Either[$[A], $[B]] => $[C])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[C] = {
      val f1: lambdas.Context ?=> $[A] => $[C] = ctx ?=> a => f(Left(a))
      val f2: lambdas.Context ?=> $[B] => $[C] = ctx ?=> b => f(Right(b))
      val a = VarDesc("Variable bound by Left pattern", pos)
      val b = VarDesc("Variable bound by Right pattern", pos)
      lambdas.switch(
        Sink[lambdas.VFun, ++, A, C]((a, f1)) <+> Sink((b, f2)),
        [X, Y] => (fx: Fun[X, C], fy: Fun[Y, C]) => either(fx, fy),
        [X, Y, Z] => (_: Unit) => distributeL[X, Y, Z],
      ) match {
        case Lambdas.Delambdified.Exact(f)      => f(ab)
        case Lambdas.Delambdified.Closure(x, f) => lambdas.Expr.mapTupled(x zip Tupled.atom(ab), f)(VarDesc("switch with captured expressions", pos))
        case Lambdas.Delambdified.Failure(e)    => raiseError(e)
      }
    }
  }

  extension [A, B](f: Fun[A, B]) {
    def apply(using SourcePos)(a: $[A])(using LambdaContext): $[B] =
      a > f

    def /\[C](g: Fun[A, C]): Fun[A, B ** C] =
      dup[A] > par(f, g)
  }

  object λ {
    def apply[A, B](using pos: SourcePos)(
      f: LambdaContext ?=> $[A] => $[B],
    ): Fun[A, B] = {
      lambdas.delambdifyTopLevel(VarDesc("The variable bound by lambda expression", pos), f) match
        case Lambdas.Delambdified.Exact(f) =>
          f
        case Lambdas.Delambdified.Closure(captured, f) =>
          throw RuntimeException(
            s"Lambda expression at ${pos.filename}:${pos.line} " +
              s"is not allowed to capture variables from an outer scope.\n" +
              s"Captured:\n" +
              printVars(lambdas.Expr.initialVars(captured))
          )
        case Lambdas.Delambdified.Failure(e) =>
          raiseError(e)
    }

    def ?[A, B](using pos: SourcePos)(
      f: LambdaContext ?=> $[A] => $[B],
    ): Fun[A, B] =
      apply(using pos) { case ?(a) => f(a) }

    def +[A, B](using pos: SourcePos)(
      f: LambdaContext ?=> $[A] => $[B],
    ): Fun[A, B] =
      apply(using pos) { case +(a) => f(a) }

    def *[A, B](using pos: SourcePos)(
      f: LambdaContext ?=> $[A] => $[B],
    ): Fun[A, B] =
      apply(using pos) { case *(a) => f(a) }
  }

  object ? {
    def unapply[A](using pos: SourcePos)(using LambdaContext)(a: $[A]): Some[$[A]] = {
      lambdas.Context.registerDiscard(a.resultVar)([X] => (_: Unit) => prj2[A, X])
      Some(a)
    }
  }

  object + {
    def unapply[A](using pos: SourcePos)(using LambdaContext)(a: $[A]): Some[$[A]] = {
      lambdas.Context.registerSplit(a.resultVar)(dup[A])
      Some(a)
    }
  }

  object * {
    def unapply[A](using pos: SourcePos)(using LambdaContext)(a: $[A]): Some[$[A]] = {
      lambdas.Context.registerSplit(a.resultVar)(dup[A])
      lambdas.Context.registerDiscard(a.resultVar)([X] => (_: Unit) => prj2[A, X])
      Some(a)
    }
  }

  def compileToScala[A, B](f: Fun[Val[A], Val[B]]): A => B =
    a => {
      evaluate(f)(Values.SingleVal(a)) match
        case Values.SingleVal(b) => b
    }

  private def printVars(vs: Var.Set[VarDesc]): String =
    vs.list
      .map(_.origin)
      .map {
        case VarDesc(desc, Some(pos)) => s" - $desc at ${pos.filename}:${pos.line}"
        case VarDesc(desc, None)      => s" - $desc"
      }
      .mkString("\n")

  private def raiseError(e: Lambdas.Error.LinearityViolation[VarDesc]): Nothing = {
    e match
      case Overused(vars) =>
        throw RuntimeException(s"Variables used more than once:\n${printVars(vars)}")
      case Underused(vars) =>
        throw RuntimeException(s"Variables not fully consumed:\n${printVars(vars)}")
      case OverUnder(overused, underused) =>
        throw RuntimeException(
          s"Variables used more than once:\n${printVars(overused)}\n" +
          s"Variables not fully consumed:\n${printVars(underused)}"
        )
  }

  private enum Values[A] {
    case SingleVal[A](value: A) extends Values[Val[A]]
    case Pair[A, B](_1: Values[A], _2: Values[B]) extends Values[A ** B]
  }

  private def evaluate[A, B](f: Fun[A, B])(a: Values[A]): Values[B] = {
    import Values.{Pair, SingleVal}

    f match
      case Id() => a
      case AndThen(f, g) => evaluate(g)(evaluate(f)(a))
      case AssocLR() => a match { case Pair(Pair(a1, a2), a3) => Pair(a1, Pair(a2, a3)) }
      case AssocRL() => a match { case Pair(a1, Pair(a2, a3)) => Pair(Pair(a1, a2), a3) }
      case Par(f1, f2) => a match { case Pair(a1, a2) => Pair(evaluate(f1)(a1), evaluate(f2)(a2)) }
      case Swap() => a match { case Pair(a1, a2) => Pair(a2, a1) }
      case IntroFst() => Pair(SingleVal(()), a)
      case IntroSnd() => Pair(a, SingleVal(()))
      case Prj1() => a match { case Pair(a1, _) => a1 }
      case Prj2() => a match { case Pair(_, a2) => a2 }
      case Dup() => Pair(a, a)
      case MapVal(f) => a match { case SingleVal(a) => SingleVal(f(a)) }
      case LiftPair() => a match { case SingleVal((a1, a2)) => Pair(SingleVal(a1), SingleVal(a2)) }
      case UnliftPair() => a match { case Pair(SingleVal(a1), SingleVal(a2)) => SingleVal((a1, a2)) }
  }
}
