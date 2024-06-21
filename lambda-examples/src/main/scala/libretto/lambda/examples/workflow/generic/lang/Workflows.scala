package libretto.lambda.examples.workflow.generic.lang

import libretto.lambda.{CapturingFun, Lambdas, Sink}
import libretto.lambda.util.SourcePos
import libretto.lambda.util.Validated.{Invalid, Valid}
import libretto.lambda.Tupled

import scala.concurrent.duration.FiniteDuration

class Workflows[Action[_, _]] {
  import Workflows.VarOrigin

  object ** {
    def unapply[A, B](using pos: SourcePos)(expr: Expr[A ** B])(using LambdaContext): (Expr[A], Expr[B]) =
      lambdas.Expr.unzip(expr)(VarOrigin.Prj1(pos), VarOrigin.Prj2(pos))
  }

  opaque type Flow[A, B] = FlowAST[Action, A, B]

  def astOf[A, B](f: Flow[A, B]): FlowAST[Action, A, B] =
    f

  extension [A, B](f: Flow[A, B]) {
    def apply(using pos: SourcePos)(a: Expr[A])(using LambdaContext): Expr[B] =
      lambdas.Expr.map(a, f)(VarOrigin.FlowAppResult(pos))

    def >>>[C](g: Flow[B, C]): Flow[A, C] =
      FlowAST.AndThen(f, g)
  }

  object Flow {

    def apply[A, B](using
      pos: SourcePos,
    )(
      f: LambdaContext ?=> Expr[A] => Expr[B],
    ): Flow[A, B] =
      lambdas.delambdifyTopLevel((), VarOrigin.LambdaAbstraction(pos), f) match {
        case Valid(CapturingFun.NoCapture(g)) => g
        case Valid(CapturingFun.Closure(x, g)) => ???
        case Invalid(e) => throw AssertionError(e)
      }

    def id[A]: Flow[A, A] =
      FlowAST.Id()

    def par[A1, A2, B1, B2](f1: Flow[A1, B1], f2: Flow[A2, B2]): Flow[A1 ** A2, B1 ** B2] =
      FlowAST.Par(f1, f2)

    def swap[A, B]: Flow[A ** B, B ** A] =
      FlowAST.Swap()

    def fst[A1, A2, B1](f: Flow[A1, B1]): Flow[A1 ** A2, B1 ** A2] =
      par(f, id)

    def introFst[X]: Flow[X, Unit ** X] =
      FlowAST.IntroFst()

    def introFst[X, A](f: Flow[Unit, A]): Flow[X, A ** X] =
      introFst[X] >>> fst(f)

    def injectL[Op[_, _], A, B]: Flow[A, A ++ B] =
      FlowAST.InjectL()

    def injectR[Op[_, _], A, B]: Flow[B, A ++ B] =
      FlowAST.InjectR()

    def either[A, B, C](f: Flow[A, C], g: Flow[B, C]): Flow[A ++ B, C] =
      FlowAST.Either(f, g)

    def distributeLR[A, B, C]: Flow[A ** (B ++ C), (A ** B) ++ (A ** C)] =
      FlowAST.DistributeLR()

    def dup[A]: Flow[A, A ** A] =
      FlowAST.Dup()

    def prj1[A, B]: Flow[A ** B, A] =
      FlowAST.Prj1()

    def prj2[A, B]: Flow[A ** B, B] =
      FlowAST.Prj2()

    def read[A]: Flow[Unit, PortName[A] ** Reading[A]] =
      FlowAST.Read()

    def readAwait[A]: Flow[Reading[A], A] =
      FlowAST.ReadAwait()

    def readAwaitTimeout[A](duration: FiniteDuration): Flow[Reading[A], A ++ Reading[A]] =
      FlowAST.ReadAwaitTimeout(duration)

    def doWhileLoop[A, B](f: Flow[A, A ++ B]): Flow[A, B] =
      FlowAST.DoWhile(f)

    def doWhile[A, B](using SourcePos)(f: LambdaContext ?=> Expr[A] => Expr[A ++ B]): Flow[A, B] =
      doWhileLoop(Flow(f))

    // TODO: not all types might be meaningfully delayable.
    // Might require a typeclass evidence.
    def delay[A](duration: FiniteDuration): Flow[A, A] =
      FlowAST.Delay(duration)

    def action[A, B](a: Action[A, B]): Flow[A, B] =
      FlowAST.Ext(a)

  }

  private val lambdas: Lambdas[Flow, **, VarOrigin, Unit] =
    Lambdas[Flow, **, VarOrigin, Unit](
      universalSplit   = Some([X] => (_: Unit) => Flow.dup[X]),
      universalDiscard = Some([X, Y] => (_: Unit) => Flow.prj2[X, Y]),
    )

  opaque type Expr[A]       = lambdas.Expr[A]
  opaque type LambdaContext = lambdas.Context

  object Expr {
    /** Alias for [[constant]]. */
    def apply[A](using SourcePos)(f: Flow[Unit, A])(using LambdaContext): Expr[A] =
      constant(f)

    def constant[A](using pos: SourcePos)(f: Flow[Unit, A])(using LambdaContext): Expr[A] =
      lambdas.Expr.const([x] => (_: Unit) => Flow.introFst[x, A](f))(VarOrigin.ConstantExpr(pos))
  }

  extension [A](a: Expr[A])
    def **[B](using pos: SourcePos)(b: Expr[B])(using LambdaContext): Expr[A ** B] =
      lambdas.Expr.zip(a, b)(VarOrigin.Tuple(pos))

  extension [A, B](expr: Expr[A ++ B])
    def switch[C](using pos: SourcePos)(
      f: LambdaContext ?=> Either[Expr[A], Expr[B]] => Expr[C],
    )(using LambdaContext): Expr[C] =
      val fa = lambdas.delambdifyNested((), VarOrigin.Left(pos),  ctx ?=> (a: Expr[A]) => f(Left(a)))
      val fb = lambdas.delambdifyNested((), VarOrigin.Right(pos), ctx ?=> (b: Expr[B]) => f(Right(b)))
      (fa zip fb)
        .flatMap { case (fa, fb) =>
          CapturingFun.compileSink(
            Sink(fa) <+> Sink(fb)
          )(lambdas.compoundDiscarder, lambdas.exprUniter)
        }
        .map {
          case CapturingFun.NoCapture(g) => g(expr)
          case CapturingFun.Closure(x, g) =>
            val xa = lambdas.Expr.zipN(Tupled.zip(x, Tupled.atom(expr)))(VarOrigin.FunctionInputWithCapturedExpressions(pos))
            lambdas.Expr.map(xa, g)(VarOrigin.CapturingSwitch(pos))
        }
        .valueOr { es => throw AssertionError(es) }

  def unit(using SourcePos, LambdaContext): Expr[Unit] =
    Expr(Flow.id[Unit])

  def returning[A](
    a: Expr[A],
    cmds: Expr[Unit]*,
  )(using
    SourcePos,
    LambdaContext,
  ): Expr[A] =
    def go(a: Expr[A], cmds: List[Expr[Unit]]): Expr[A] =
      cmds match
        case Nil     => a
        case c :: cs => go(Flow.prj1(a ** c), cs)
    go(a, cmds.toList)
}

object Workflows:

  private[Workflows] enum VarOrigin:
    case LambdaAbstraction(pos: SourcePos)
    case FlowAppResult(pos: SourcePos)
    case ConstantExpr(pos: SourcePos)
    case Tuple(pos: SourcePos)
    case Prj1(pos: SourcePos)
    case Prj2(pos: SourcePos)
    case Left(pos: SourcePos)
    case Right(pos: SourcePos)
    case CapturingSwitch(pos: SourcePos)
    case FunctionInputWithCapturedExpressions(pos: SourcePos)
