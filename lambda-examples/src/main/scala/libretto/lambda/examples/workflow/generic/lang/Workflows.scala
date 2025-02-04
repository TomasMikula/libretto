package libretto.lambda.examples.workflow.generic.lang

import libretto.lambda.{CapturingFun, CoproductPartitioning, EnumModule, Lambdas, Member, PatternMatching, Sink}
import libretto.lambda.util.{BiInjective, NonEmptyList, SourcePos, Validated}
import libretto.lambda.util.Validated.{Invalid, Valid, invalid}
import libretto.lambda.Tupled

import scala.concurrent.duration.FiniteDuration

class Workflows[Action[_, _]] {
  import Workflows.VarOrigin

  object ** {
    def unapply[A, B](using pos: SourcePos)(expr: Expr[A ** B])(using LambdaContext): (Expr[A], Expr[B]) =
      lambdas.Expr.unzip(expr)(VarOrigin.Prj1(pos), VarOrigin.Prj2(pos))
  }

  opaque type Flow[A, B] = FlowAST[Action, A, B]

  private type Extractor[A, B] = libretto.lambda.Extractor[Flow, **, A, B]
  private case class ExtractorOccurrence[A, B](pos: SourcePos, extractor: Extractor[A, B])
  private type PartialFlow[A, B] = Flow[A, B] | ExtractorOccurrence[A, B]

  def astOf[A, B](f: Flow[A, B]): FlowAST[Action, A, B] =
    f

  extension [A, B](f: Flow[A, B]) {
    def ast: FlowAST[Action, A, B] =
      f

    def shakeUp: Flow[A, B] =
      FlowAST.shakeUp(f)
  }

  private val lambdas: Lambdas[PartialFlow, **, VarOrigin, Unit] =
    Lambdas[PartialFlow, **, VarOrigin, Unit](
      universalSplit   = Some([X] => (_: DummyImplicit) ?=> Flow.dup[X]),
      universalDiscard = Some([X, Y] => (_: DummyImplicit) ?=> (Flow.prj2[X, Y], Flow.prj1[Y, X])),
    )

  private val patmat =
    new PatternMatching[Flow, **]

  private val patmatForLambdas =
    patmat.forLambdas(lambdas)(
      isExtractor = [X, Y] => (f: PartialFlow[X, Y]) =>
        f match {
          case o: ExtractorOccurrence[X, Y] => Some(o.extractor)
          case _ => None
        },
      lower =
        [X, Y] => (f: PartialFlow[X, Y]) =>
          f match {
            case f: Flow[X, Y] => Valid(f)
            case ExtractorOccurrence(p, e) => invalid(MisplacedExtractor(p, e))
          },
      lift = [X, Y] => (f: Flow[X, Y]) => (f: PartialFlow[X, Y]),
    )

  val Enum =
    EnumModule[Flow, **, Enum, ||, ::]

  opaque type Expr[A]       = lambdas.Expr[A]
  opaque type LambdaContext = lambdas.Context

  import lambdas.LinearityViolation
  import lambdas.shuffled.{Shuffled as ~>}

  private case class MisplacedExtractor(pos: SourcePos, ext: Extractor[?, ?])
  private case class IllegalCapture[X](pos: SourcePos, captured: Tupled[**, Expr, X])
  private type UnusedInBranch = PatternMatching.UnusedInBranch[VarOrigin, Unit]

  private type CapturingFun[A, B] = libretto.lambda.CapturingFun[Flow, **, Tupled[**, Expr, _], A, B]

  private def total[A, B](f: PartialFlow[A, B]): Validated[MisplacedExtractor, Flow[A, B]] =
    f match
      case f: Flow[A, B] => Valid(f)
      case ExtractorOccurrence(pos, ext) => invalid(MisplacedExtractor(pos, ext))

  private def foldTotal[A, B](f: lambdas.Delambdified[A, B]): Validated[MisplacedExtractor, CapturingFun[A, B]] =
    import CapturingFun.{Closure, NoCapture}

    f match
      case NoCapture(f)  => f.foldMapA([x, y] => total(_)).map(NoCapture(_))
      case Closure(x, f) => f.foldMapA([x, y] => total(_)).map(Closure(x, _))


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
      compile(pos, f)
        .valueOr { es => throw NotImplementedError(s"Unhandled assembly errors: $es") }

    private def compile[A, B](
      pos: SourcePos,
      f: LambdaContext ?=> Expr[A] => Expr[B],
    ): Validated[
      LinearityViolation | MisplacedExtractor | IllegalCapture[?],
      Flow[A, B]
    ] =
      lambdas
        .delambdifyTopLevel((), VarOrigin.LambdaAbstraction(pos), f)
        .flatMap(foldTotal)
        .flatMap {
          case CapturingFun.NoCapture(g) => Valid(g)
          case CapturingFun.Closure(x, g) => invalid(IllegalCapture(pos, x))
        }

    def id[A]: Flow[A, A] =
      FlowAST.Id()

    def par[A1, A2, B1, B2](f1: Flow[A1, B1], f2: Flow[A2, B2]): Flow[A1 ** A2, B1 ** B2] =
      FlowAST.Par(f1, f2)

    def swap[A, B]: Flow[A ** B, B ** A] =
      FlowAST.Swap()

    def fst[A1, A2, B1](f1: Flow[A1, B1]): Flow[A1 ** A2, B1 ** A2] =
      par(f1, id)

    def snd[A1, A2, B2](f2: Flow[A2, B2]): Flow[A1 ** A2, A1 ** B2] =
      par(id, f2)

    def introFst[X]: Flow[X, Unit ** X] =
      FlowAST.IntroFst()

    def introFst[X, A](f: Flow[Unit, A]): Flow[X, A ** X] =
      introFst[X] >>> fst(f)

    def introSnd[X]: Flow[X, X ** Unit] =
      FlowAST.IntroSnd()

    def introSnd[X, A](f: Flow[Unit, A]): Flow[X, X ** A] =
      introSnd[X] >>> snd(f)

    def injectL[Op[_, _], A, B]: Flow[A, A ++ B] =
      FlowAST.InjectL()

    def injectR[Op[_, _], A, B]: Flow[B, A ++ B] =
      FlowAST.InjectR()

    def either[A, B, C](f: Flow[A, C], g: Flow[B, C]): Flow[A ++ B, C] =
      FlowAST.Either(f, g)

    def inject[Label, A, Cases](i: Member[||, ::, Label, A, Cases]): Flow[A, Enum[Cases]] =
      FlowAST.Inject(i)

    def distributeLR[A, B, C]: Flow[A ** (B ++ C), (A ** B) ++ (A ** C)] =
      FlowAST.DistributeLR()

    def distributeRL[A, B, C]: Flow[(A ++ B) ** C, (A ** C) ++ (B ** C)] =
      FlowAST.DistributeRL()

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

  object Expr {
    /** Alias for [[constant]]. */
    def apply[A](using SourcePos)(f: Flow[Unit, A])(using LambdaContext): Expr[A] =
      constant(f)

    def constant[A](using pos: SourcePos)(f: Flow[Unit, A])(using LambdaContext): Expr[A] =
      lambdas.Expr.const(
        [x] => _ ?=> Flow.introFst[x, A](f),
        [x] => _ ?=> Flow.introSnd[x, A](f),
      )(VarOrigin.ConstantExpr(pos))
  }

  class Case[A, R](
    val pos: SourcePos,
    val f: LambdaContext ?=> Expr[A] => Expr[R],
  )

  def is[A, R](using pos: SourcePos)(f: LambdaContext ?=> Expr[A] => Expr[R]): Case[A, R] =
    Case(pos, f)

  extension [A](a: Expr[A])
    def **[B](using pos: SourcePos)(b: Expr[B])(using LambdaContext): Expr[A ** B] =
      lambdas.Expr.zip(a, b)(VarOrigin.Tuple(pos))

    infix def switch[R](using switchPos: SourcePos, ctx: LambdaContext)(
      case0: Case[A, R],
      cases: Case[A, R]*
    ): Expr[R] =
      patmatForLambdas
        .delambdifyAndCompile(
          a,
          VarOrigin.CapturingSwitch(switchPos),
          VarOrigin.SwitchResult(switchPos),
          NonEmptyList(case0, cases.toList)
            .map { c => ((), VarOrigin.SwitchCase(c.pos), c.f) }
        )
        .valueOr { es => raiseErrors(s"Failed to compile pattern match at ${switchPos.filename}:${switchPos.line}", es) }

  private val EitherPartitioning =
    CoproductPartitioning[Flow, **, ++]("InL", "InR")

  def InL[A, B]: Extractor[A ++ B, A] =
    EitherPartitioning.Inl[A, B]

  def InR[A, B]: Extractor[A ++ B, B] =
    EitherPartitioning.Inr[A, B]

  extension [A, B](ext: Extractor[A, B]) {
    def unapply(using pos: SourcePos, ctx: LambdaContext)(a: Expr[A]): Some[Expr[B]] =
      val b = lambdas.Expr.map(a, ExtractorOccurrence(pos, ext))(VarOrigin.ExtractorResult(pos))

      // register an explicit discarder, so that delambdification of
      //   case Foo(_) => bar
      // knows about the pattern `Foo(_)` and does not treat the case as
      //   case _ => bar
      lambdas.Context.registerDiscard(b)(
        [Y] => _ ?=> Flow.prj2[B, Y],
        [Y] => _ ?=> Flow.prj1[Y, B],
      )

      Some(b)

    def apply(using pos: SourcePos, ctx: LambdaContext)(b: Expr[B]): Expr[A] =
      lambdas.Expr.map(b, ext.reinject)(VarOrigin.ConstructorResult(pos))

    def apply(): Flow[B, A] =
      ext.reinject
  }

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

  private class AssemblyError(msg: String) extends Exception(msg)

  private def raiseErrors(
    summary: String,
    es: NonEmptyList[lambdas.LinearityViolation | UnusedInBranch | MisplacedExtractor | patmat.PatternMatchError]
  ): Nothing =
    val msg = formatMessages(es)
    throw AssemblyError(summary + "\n" + msg)

  private def formatMessages(es: NonEmptyList[lambdas.LinearityViolation | UnusedInBranch | MisplacedExtractor | patmat.PatternMatchError]): String =
    es
      .map { e =>
        val NonEmptyList(line0, lines) = formatMessage(e)
        (s"- $line0" :: lines.map("  " + _))
          .mkString("\n")
      }
      .toList
      .mkString("\n")

  private def formatMessage(e: lambdas.LinearityViolation | UnusedInBranch | MisplacedExtractor | patmat.PatternMatchError): NonEmptyList[String] =
    e match
      case e: lambdas.LinearityViolation =>
        ???
      case e: UnusedInBranch =>
        ???
      case MisplacedExtractor(pos, ext) =>
        NonEmptyList.of(s"Extractor ${ext.show} used outside pattern match (at ${pos.filename}:${pos.line})")
      case e: patmat.PatternMatchError =>
        ???
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
    case FunctionInputWithCapturedExpressions(pos: SourcePos)
    case CapturingSwitch(pos: SourcePos)
    case SwitchResult(switchPos: SourcePos)
    case SwitchCase(pos: SourcePos)
    case ExtractorResult(pos: SourcePos)
    case ConstructorResult(pos: SourcePos)
