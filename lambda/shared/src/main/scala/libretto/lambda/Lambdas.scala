package libretto.lambda

import libretto.lambda.Lambdas.LinearityViolation
import libretto.lambda.util.{Applicative, BiInjective, Exists, NonEmptyList, UniqueTypeArg, Validated}
import libretto.lambda.util.Validated.{Invalid, Valid, invalid}
import scala.annotation.targetName

/**
  * @tparam V information associated with variables
  * @tparam C information associated with lambda contexts (scopes)
  */
trait Lambdas[-⚬[_, _], |*|[_, _], V, C] {
  final type Tupled[F[_], A] = libretto.lambda.Tupled[|*|, F, A]

  type Expr[A]
  val Expr: Exprs

  trait Exprs {
    def variable[A](a: Var[V, A]): Expr[A]
    def map[A, B](e: Expr[A], f: A -⚬ B)(resultVarName: V)(using Context): Expr[B]
    def zip[A, B](a: Expr[A], b: Expr[B])(resultVarName: V)(using Context): Expr[A |*| B]
    def zipN[A](a: Tupled[Expr, A])(resultVarName: V)(using Context): Expr[A]
    def unzip[A, B](ab: Expr[A |*| B])(varName1: V, varName2: V)(using Context): (Expr[A], Expr[B])
    def const[A](introduce: [x] => Unit => x -⚬ (A |*| x))(varName: V)(using Context): Expr[A]

    def resultVar[A](a: Expr[A]): Var[V, A]
    def initialVars[A](a: Expr[A]): Var.Set[V]

    def initialVars[A](as: Tupled[Expr, A]): Var.Set[V] =
      as.foldMap0([x] => (x: Expr[x]) => initialVars(x), _ merge _)
  }

  extension [A](a: Expr[A]) {
    @targetName("exprMap")
    infix def map[B](f: A -⚬ B)(resultVar: V)(using Context): Expr[B] =
      Expr.map(a, f)(resultVar)

    @targetName("exprZip")
    infix def zip[B](b: Expr[B])(resultVar: V)(using Context): Expr[A |*| B] =
      Expr.zip(a, b)(resultVar)

    @targetName("exprResultVar")
    def resultVar: Var[V, A] =
      Expr.resultVar(a)
  }

  given UniqueTypeArg[Expr] with {
    override def testEqual[A, B](a: Expr[A], b: Expr[B]): Option[A =:= B] =
      summon[UniqueTypeArg[Var[V, _]]].testEqual(a.resultVar, b.resultVar)
  }

  type Context
  val Context: Contexts

  trait Contexts {
    def fresh(info: C): Context

    def nested(info: C, parent: Context): Context

    def info(using ctx: Context): C

    def newVar[A](label: V)(using Context): Var[V, A]

    def isDefiningFor[A](v: Var[V, A])(using ctx: Context): Boolean

    def registerNonLinearOps[A](a: Expr[A])(
      split: Option[A -⚬ (A |*| A)],
      discard: Option[[B] => Unit => (A |*| B) -⚬ B],
    )(using
      Context
    ): Unit

    def registerConstant[A](v: Var[V, A])(
      introduce: [x] => Unit => x -⚬ (A |*| x),
    )(using ctx: Context): Unit

    def getSplit[A](v: Var[V, A])(using Context): Option[A -⚬ (A |*| A)]

    def getDiscard[A](v: Var[V, A])(using Context): Option[[B] => Unit => (A |*| B) -⚬ B]

    def getConstant[A](v: Var[V, A])(using Context): Option[[x] => Unit => x -⚬ (A |*| x)]

    def registerSplit[A](a: Expr[A])(split: A -⚬ (A |*| A))(using Context): Unit =
      registerNonLinearOps(a)(Some(split), None)

    def registerDiscard[A](a: Expr[A])(discard: [B] => Unit => (A |*| B) -⚬ B)(using Context): Unit =
      registerNonLinearOps(a)(None, Some(discard))
  }

  type Delambdified[A, B] = Lambdas.Delambdified[Expr, |*|, -⚬, V, C, A, B]
  type DelambdifiedSuccess[A, B] = Lambdas.Delambdified.Success[Expr, |*|, -⚬, V, C, A, B]

  protected def eliminateLocalVariables[A, B](
    boundVar: Var[V, A],
    expr: Expr[B],
  )(using Context): Delambdified[A, B]

  private def delambdify[A, B](
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  )(using Context): Delambdified[A, B] = {
    val bindVar = Context.newVar[A](varName)
    eliminateLocalVariables(bindVar, f(Expr.variable(bindVar)))
  }

  def delambdifyTopLevel[A, B](
    freshCtxInfo: C,
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  ): Delambdified[A, B] =
    delambdify(varName, f)(using Context.fresh(freshCtxInfo))

  def delambdifyNested[A, B](
    nestedCtxInfo: C,
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  )(using parent: Context): Delambdified[A, B] =
    delambdify(varName, f)(using Context.nested(nestedCtxInfo, parent = parent))

  type VFun[A, B] = (C, V, Context ?=> Expr[A] => Expr[B])

  def switch[<+>[_, _], A, B](
    cases: Sink[VFun, <+>, A, B],
    sum: [X, Y] => (X -⚬ B, Y -⚬ B) => (X <+> Y) -⚬ B,
    distribute: [X, Y, Z] => Unit => (X |*| (Y <+> Z)) -⚬ ((X |*| Y) <+> (X |*| Z))
  )(using
    Context,
  ): Delambdified[A, B]

  protected def switchImpl[<+>[_, _], A, B](
    cases: Sink[VFun, <+>, A, B],
    sum: [X, Y] => (X -⚬ B, Y -⚬ B) => (X <+> Y) -⚬ B,
    distribute: [X, Y, Z] => Unit => (X |*| (Y <+> Z)) -⚬ ((X |*| Y) <+> (X |*| Z))
  )(using
    BiInjective[|*|],
    SymmetricSemigroupalCategory[-⚬, |*|],
    Context,
  ): Delambdified[A, B] = {
    val cases1: Sink[Delambdified, <+>, A, B] =
      cases.map[Delambdified] { [X] => (vf: VFun[X, B]) =>
        delambdifyNested(vf._1, vf._2, vf._3)
      }

    cases1.reduce(
      [x, y] => (f1: Delambdified[x, B], f2: Delambdified[y, B]) => {
        import Lambdas.Delambdified.{Closure, Exact, Failure}
        (f1, f2) match {
          case (Exact(f1), Exact(f2)) =>
            Exact(sum(f1, f2))
          case (Closure(x, f1), Exact(f2)) =>
            discarderOf(x) match
              case Right(discardFst) => Closure(x, distribute(()) > sum(f1, discardFst(()) > f2))
              case Left(unusedVars)  => Failure(LinearityViolation.UnusedInBranch(unusedVars))
          case (Exact(f1), Closure(y, f2)) =>
            discarderOf(y) match
              case Right(discardFst) => Closure(y, distribute(()) > sum(discardFst(()) > f1, f2))
              case Left(unusedVars)  => Failure(LinearityViolation.UnusedInBranch(unusedVars))
          case (Closure(x, f1), Closure(y, f2)) =>
            union(x, y) match
              case Valid(Exists.Some((p, p1, p2))) =>
                Closure(p, distribute(()) > sum(p1.inFst > f1, p2.inFst > f2))
              case Invalid(e) =>
                Failure(e)
          case (Failure(e1), Failure(e2)) =>
            Failure(e1 ++ e2)
          case (Failure(e1), _) =>
            Failure(e1)
          case (_, Failure(e2)) =>
            Failure(e2)
        }
      }
    )
  }

  def leastCommonCapture[A, B](
    fs: NonEmptyList[DelambdifiedSuccess[A, B]],
  )(using
    ctx: Context,
    ssc: SymmetricSemigroupalCategory[-⚬, |*|],
    inj: BiInjective[|*|],
  ): Lambdas.Delambdified[Expr, |*|, [a, b] =>> NonEmptyList[a -⚬ b], V, C, A, B] =
    leastCommonCapture(fs.head, fs.tail)

  def leastCommonCapture[A, B](
    head: DelambdifiedSuccess[A, B],
    tail: List[DelambdifiedSuccess[A, B]],
  )(using
    ctx: Context,
    ssc: SymmetricSemigroupalCategory[-⚬, |*|],
    inj: BiInjective[|*|],
  ): Lambdas.Delambdified[Expr, |*|, [a, b] =>> NonEmptyList[a -⚬ b], V, C, A, B] = {
    import Lambdas.Delambdified.{Closure, Exact, Failure}

    tail match {
      case Nil =>
        head.mapFun[[a, b] =>> NonEmptyList[a -⚬ b]]([X] => NonEmptyList(_, Nil))
      case f1 :: fs =>
        head match
          case Exact(f0) =>
            leastCommonCapture(f1, fs) match
              case Exact(fs) =>
                Exact(f0 :: fs)
              case Closure(captured, fs) =>
                discarderOf(captured) match
                  case Right(discardFst) => Closure(captured, (discardFst(()) > f0) :: fs)
                  case Left(unusedVars)  => Failure(LinearityViolation.UnusedInBranch(unusedVars))
              case Failure(e) =>
                Failure(e)

          case Closure(captured, f) =>
            leastCommonCapture(captured, tail) match
              case Invalid(e) =>
                Failure(e)
              case Valid(Exists.Some((p, Closure(y, fs)))) =>
                Closure(y, NonEmptyList(ssc.fst(p) > f, fs))
    }
  }

  private def leastCommonCapture[X, A, B](
    acc: Tupled[Expr, X],
    fs: List[DelambdifiedSuccess[A, B]],
  )(using
    ctx: Context,
    ssc: SymmetricSemigroupalCategory[-⚬, |*|],
    inj: BiInjective[|*|],
  ): Validated[
    LinearityViolation[V, C],
    Exists[[Y] =>> (
      Y -⚬ X,
      Lambdas.Delambdified.Closure[Expr, |*|, [a, b] =>> List[a -⚬ b], V, C, Y, A, B]
    )]
  ] = {
    import Lambdas.Delambdified.{Closure, Exact, Failure}

    fs match
      case Nil =>
        Valid(Exists(ssc.id[X], Closure(acc, Nil)))
      case f :: fs =>
        f match
          case Exact(f) =>
            discarderOf(acc) match
              case Left(unusedVars) =>
                invalid(LinearityViolation.UnusedInBranch(unusedVars))
              case Right(discardFst) =>
                val g = discardFst(()) > f
                leastCommonCapture(acc, fs)
                  .map { case Exists.Some((p, Closure(y, gs))) =>
                    Exists(p, Closure(y, (ssc.fst(p) > g) :: gs))
                  }

          case Closure(captured, f) =>
            union(acc, captured)
              .flatMap { case Exists.Some((y, p1, p2)) =>
                leastCommonCapture(y, fs)
                  .map { case Exists.Some((q, Closure(z, gs))) =>
                    Exists((q > p1, Closure(z, (ssc.fst(q > p2) > f) :: gs)))
                  }
              }
  }

  private def discarderOf[A](a: Tupled[Expr, A])(using
    ctx: Context,
    ssc: SymmetricSemigroupalCategory[-⚬, |*|],
  ): Either[Var.Set[V], [B] => Unit => (A |*| B) -⚬ B] =
    a.asBin match {
      case Bin.Leaf(x) =>
        val v = x.resultVar
        Context.getDiscard(v) match
          case Some(discardFst) => Right(discardFst)
          case None             => Left(Var.Set(v))
      case Bin.Branch(l, r) =>
        (discarderOf(Tupled.fromBin(l)), discarderOf(Tupled.fromBin(r))) match
          case (Right(f), Right(g)) => Right([B] => (_: Unit) => ssc.fst(f(())) > g[B](()))
          case (Right(_), Left(ws)) => Left(ws)
          case (Left(vs), Right(_)) => Left(vs)
          case (Left(vs), Left(ws)) => Left(vs merge ws)
    }

  private def union[A, B](
    a: Tupled[Expr, A],
    b: Tupled[Expr, B],
  )(using
    Context,
    BiInjective[|*|],
    SymmetricSemigroupalCategory[-⚬, |*|],
  ): Validated[
    LinearityViolation[V, C],
    Exists[[P] =>> (Tupled[Expr, P], P -⚬ A, P -⚬ B)]
  ] = {
    type LinCheck[A] = Validated[LinearityViolation[V, C], A]
    type LinChecked[X, Y] = LinCheck[X -⚬ Y]
    given shuffled: Shuffled[LinChecked, |*|] = Shuffled[LinChecked, |*|]
    given Shuffled.With[-⚬, |*|, shuffled.shuffle.type] = Shuffled[-⚬, |*|](shuffled.shuffle)

    val discardFst: [X, Y] => Expr[X] => LinChecked[X |*| Y, Y] =
      [X, Y] => (x: Expr[X]) =>
        Context.getDiscard(x.resultVar) match {
          case Some(discardFst) => Valid(discardFst[Y](()))
          case None             => invalid(LinearityViolation.unusedInBranch(x.resultVar))
        }

    (a union b)(discardFst) match
      case Exists.Some((p, p1, p2)) =>
        Applicative[LinCheck].map2(
          p1.traverse[LinCheck, -⚬]([x, y] => (f: LinChecked[x, y]) => f),
          p2.traverse[LinCheck, -⚬]([x, y] => (f: LinChecked[x, y]) => f),
        ) { (p1, p2) =>
          Exists((p, p1.fold, p2.fold))
        }
  }
}

object Lambdas {
  def apply[-⚬[_, _], |*|[_, _], VarLabel, CtxLabel](
    universalSplit  : Option[[X]    => Unit => X -⚬ (X |*| X)] = None,
    universalDiscard: Option[[X, Y] => Unit => (X |*| Y) -⚬ Y] = None,
  )(using
    ssc: SymmetricSemigroupalCategory[-⚬, |*|],
    inj: BiInjective[|*|],
  ): Lambdas[-⚬, |*|, VarLabel, CtxLabel] =
    new LambdasImpl[-⚬, |*|, VarLabel, CtxLabel](
      universalSplit,
      universalDiscard,
    )

  enum LinearityViolation[VarLabel, CtxLabel]:
    case Overused(vars: Var.Set[VarLabel])
    case Unused(v: Var[VarLabel, ?], exitedCtx: CtxLabel)
    case UnusedInBranch(vars: Var.Set[VarLabel])

  object LinearityViolation {
    def overusedVar[V, C, A](v: Var[V, A]): LinearityViolation[V, C] =
      Overused(Var.Set(v))

    def unusedVar[V, C, A](v: Var[V, A], exitedCtx: C): LinearityViolation[V, C] =
      Unused(v, exitedCtx)

    def unusedInBranch[V, C, A](v: Var[V, A]): LinearityViolation[V, C] =
      UnusedInBranch(Var.Set(v))
  }

  sealed trait Delambdified[Exp[_], |*|[_, _], ->[_, _], V, C, A, B] {
    import Delambdified.*

    def mapExpr[Exp2[_]](g: [X] => Exp[X] => Exp2[X]): Delambdified[Exp2, |*|, ->, V, C, A, B] =
      this match {
        case Exact(f)             => Exact(f)
        case Closure(captured, f) => Closure(captured.trans(g), f)
        case Failure(e)           => Failure(e)
      }

    def mapFun[->>[_, _]](g: [X] => (X -> B) => (X ->> B)): Delambdified[Exp, |*|, ->>, V, C, A, B] =
      this match {
        case Exact(f)      => Exact(g(f))
        case Closure(x, f) => Closure(x, g(f))
        case Failure(e)    => Failure(e)
      }

    def toEither: Either[
      NonEmptyList[LinearityViolation[V, C]],
      CapturingFun[->, |*|, Tupled[|*|, Exp, *], A, B]
    ] =
      this match {
        case Exact(f)      => Right(CapturingFun.NoCapture(f))
        case Closure(x, f) => Right(CapturingFun.Closure(x, f))
        case Failure(e)    => Left(e)
      }
  }

  object Delambdified {
    sealed trait Success[Exp[_], |*|[_, _], ->[_, _], V, C, A, B] extends Delambdified[Exp, |*|, ->, V, C, A, B]

    case class Exact[Exp[_], |*|[_, _], ->[_, _], V, C, A, B](
      f: A -> B,
    ) extends Delambdified.Success[Exp, |*|, ->, V, C, A, B]

    case class Closure[Exp[_], |*|[_, _], ->[_, _], V, C, X, A, B](
      captured: Tupled[|*|, Exp, X],
      f: (X |*| A) -> B,
    ) extends Delambdified.Success[Exp, |*|, ->, V, C, A, B]

    case class Failure[Exp[_], |*|[_, _], ->[_, _], V, C, A, B](
      errors: NonEmptyList[LinearityViolation[V, C]],
    ) extends Delambdified[Exp, |*|, ->, V, C, A, B]

    object Failure {
      def apply[Exp[_], |*|[_, _], ->[_, _], V, C, A, B](
        e: LinearityViolation[V, C],
      ): Delambdified[Exp, |*|, ->, V, C, A, B] =
        Failure(NonEmptyList.of(e))
    }
  }
}
