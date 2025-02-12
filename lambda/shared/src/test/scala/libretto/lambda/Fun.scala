package libretto.lambda

import libretto.lambda.Lambdas.LinearityViolation.{Overused, Unused}
import libretto.lambda.util.{BiInjective, Exists, NonEmptyList, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.util.Validated.{Invalid, Valid, invalid}

sealed trait Fun[A, B] {
  def >[C](that: Fun[B, C]): Fun[A, C] = Fun.andThen(this, that)
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
  case class InjectL[A, B]() extends Fun[A, A ++ B]
  case class InjectR[A, B]() extends Fun[B, A ++ B]
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

  given cat: SymmetricSemigroupalCategory[Fun, **] with {
    override def id[A]: Fun[A, A] = Fun.id[A]
    override def andThen[A, B, C](f: Fun[A, B], g: Fun[B, C]): Fun[A, C] = Fun.andThen(f, g)
    override def assocLR[A, B, C]: Fun[(A ** B) ** C, A ** (B ** C)] = Fun.assocLR
    override def assocRL[A, B, C]: Fun[A ** (B ** C), (A ** B) ** C] = Fun.assocRL
    override def par[A1, A2, B1, B2](f1: Fun[A1, B1], f2: Fun[A2, B2]): Fun[A1 ** A2, B1 ** B2] = Fun.par(f1, f2)
    override def swap[A, B]: Fun[A ** B, B ** A] = Fun.swap
  }

  given cocat: CocartesianSemigroupalCategory[Fun, ++] with {
    override def id[A]: Fun[A, A] = Fun.id[A]
    override def andThen[A, B, C](f: Fun[A, B], g: Fun[B, C]): Fun[A, C] = Fun.andThen(f, g)
    override def injectL[A, B]: Fun[A, A ++ B] = InjectL()
    override def injectR[A, B]: Fun[B, A ++ B] = InjectR()
    override def either[A, B, C](f: Fun[A, C], g: Fun[B, C]): Fun[A ++ B, C] = HandleEither(f, g)
  }

  given Distribution[Fun, **, ++] with {
    override val cat: SemigroupalCategory[Fun, [A, B] =>> A ** B] = Fun.cat
    override def distLR[A, B, C]: Fun[A ** (B ++ C), A ** B ++ A ** C] = distributeL
    override def distRL[A, B, C]: Fun[(A ++ B) ** C, A ** C ++ B ** C] = swap > distributeL > cocat.par(swap, swap)
  }

  private case class VarDesc(desc: String, pos: Option[SourcePos])
  private object VarDesc {
    def apply(desc: String, pos: SourcePos): VarDesc =
      VarDesc(desc, Some(pos))

    def apply(desc: String): VarDesc =
      VarDesc(desc, None)
  }

  private val lambdas: Lambdas[Fun, **, VarDesc, Unit] =
    Lambdas[Fun, **, VarDesc, Unit]()

  opaque type $[A] = lambdas.Expr[A]
  opaque type LambdaContext = lambdas.Context

  def one(using pos: SourcePos, ctx: LambdaContext): $[One] =
    lambdas.Expr.const[One](
      introFst = [X] => _ ?=> introFst[X],
      introSnd = [X] => _ ?=> introSnd[X],
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
      val a = VarDesc("Variable bound by Left pattern", pos)
      val b = VarDesc("Variable bound by Right pattern", pos)
      val fa = lambdas.delambdifyFoldNested((), a, ctx ?=> (a: $[A]) => f(Left(a)))
      val fb = lambdas.delambdifyFoldNested((), b, ctx ?=> (b: $[B]) => f(Right(b)))
      (fa zip fb)
        .flatMap { case (fa, fb) =>
          val sa = Sink[[x, y] =>> (Unit, CapturingFun[Fun, **, Tupled[**, $, _], x, y]), ++, A, C](((), fa))
          val sb = Sink[[x, y] =>> (Unit, CapturingFun[Fun, **, Tupled[**, $, _], x, y]), ++, B, C](((), fb))
          CapturingFun.compileSink[Fun, **, ++, $, Unit, A ++ B, C](sa <+> sb)(
            [X] => x => lambdas.Context.exprDiscarders(x).map(_._1)
          ).emap { case ((), vs) => unusedInBranch(vs) }
        }
        .map {
          case CapturingFun.NoCapture(f)  => f(ab)
          case CapturingFun.Closure(x, f) => lambdas.Expr.map(lambdas.Expr.zipN(x zip Tupled.atom(ab))(VarDesc("function input with captured expressions")), f)(VarDesc("switch with captured expressions", pos))
        }
        .valueOr(raiseErrors)
    }
  }

  extension [A, B](f: Fun[A, B]) {
    def apply(using SourcePos)(a: $[A])(using LambdaContext): $[B] =
      a > f

    def /\[C](g: Fun[A, C]): Fun[A, B ** C] =
      andThen(dup[A], par(f, g))
  }

  object λ {
    def apply[A, B](using pos: SourcePos)(
      f: LambdaContext ?=> $[A] => $[B],
    ): Fun[A, B] = {
      lambdas.delambdifyFoldTopLevel((), VarDesc("The variable bound by lambda expression", pos), f) match
        case Valid(CapturingFun.NoCapture(f)) =>
          f
        case Valid(CapturingFun.Closure(captured, f)) =>
          throw RuntimeException(
            s"Lambda expression at ${pos.filename}:${pos.line} " +
              s"is not allowed to capture variables from an outer scope.\n" +
              s"Captured:\n" +
              printVars(lambdas.Expr.initialVars(captured))
          )
        case Invalid(es) =>
          raiseErrors(es)
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
      lambdas.Context.registerDiscard(a)(
        [X] => _ ?=> prj2[A, X],
        [X] => _ ?=> prj1[X, A],
      )
      Some(a)
    }
  }

  object + {
    def unapply[A](using pos: SourcePos)(using LambdaContext)(a: $[A]): Some[$[A]] = {
      lambdas.Context.registerSplit(a)(dup[A])
      Some(a)
    }
  }

  object * {
    def unapply[A](using pos: SourcePos)(using LambdaContext)(a: $[A]): Some[$[A]] = {
      lambdas.Context.registerSplit(a)(dup[A])
      lambdas.Context.registerDiscard(a)(
        [X] => _ ?=> prj2[A, X],
        [X] => _ ?=> prj1[X, A],
      )
      Some(a)
    }
  }

  def compileToScala[A, B](f: Fun[Val[A], Val[B]]): A => B =
    a => {
      evaluate(f)(Values.SingleVal(a)) match
        case Values.SingleVal(b) => b
    }

  private case class UnusedInBranch(vars: Var.Set[VarDesc])

  private def unusedInBranch(vs: NonEmptyList[Exists[lambdas.Expr[_]]]): UnusedInBranch =
    UnusedInBranch(Var.Set.fromList(vs.toList.map(_.value.resultVar)))

  private def printVar[A](v: Var[VarDesc, A]): String =
    v.origin match
      case VarDesc(desc, Some(pos)) => s"$desc at ${pos.filename}:${pos.line}"
      case VarDesc(desc, None)      => desc

  private def printVars(vs: Var.Set[VarDesc]): String =
    vs.list.map(v => s" - ${printVar(v)}").mkString("\n")

  private def raiseErrors(
    es: NonEmptyList[Lambdas.LinearityViolation[VarDesc, Unit] | UnusedInBranch],
  ): Nothing = {
    val msgs =
      es.flatMap:
        case Overused(vars, ()) =>
          NonEmptyList.of(s"Variables used more than once:\n${printVars(vars)}")
        case Unused(v, ()) =>
          NonEmptyList.of(s"Unused variable: ${printVar(v)}")
        case UnusedInBranch(vs) =>
          NonEmptyList.of(s"Variables not used in all branches:\n${printVars(vs)}")
    val msg = msgs.toList.mkString("\n")
    throw RuntimeException(msg)
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
