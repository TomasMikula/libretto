package libretto.lambda.examples.workflow.generic.lang

import libretto.lambda.{Lambdas, Sink, SymmetricSemigroupalCategory}
import libretto.lambda.Lambdas.Abstracted
import libretto.lambda.util.{BiInjective, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.Tupled

/** A domain-level pair.
  *
  * Uninhabited, used only as a (phantom) type index.
  */
sealed trait **[A, B]

given BiInjective[**] with {
  override def unapply[A, B, X, Y](ev: A ** B =:= X ** Y): (A =:= X, B =:= Y) =
    ev match { case TypeEq(Refl()) => (summon, summon) }
}

/** A domain-level `Either`.
  *
  * Uninhabited, used only as a (phantom) type index.
  */
sealed trait ++[A, B]

sealed trait ReceptorEndpointDesc[A]

sealed trait FlowAST[Op[_, _], A, B] {
  def >>>[C](that: FlowAST[Op, B, C]): FlowAST[Op, A, C] =
    FlowAST.AndThen(this, that)
}

object FlowAST {
  case class Id[Op[_, _], A]() extends FlowAST[Op, A, A]
  case class AndThen[Op[_, _], A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]) extends FlowAST[Op, A, C]
  case class AssocLR[Op[_, _], A, B, C]() extends FlowAST[Op, (A ** B) ** C, A ** (B ** C)]
  case class AssocRL[Op[_, _], A, B, C]() extends FlowAST[Op, A ** (B ** C), (A ** B) ** C]
  case class Par[Op[_, _], A1, A2, B1, B2](f1: FlowAST[Op, A1, B1], f2: FlowAST[Op, A2, B2]) extends FlowAST[Op, A1 ** A2, B1 ** B2]
  case class Swap[Op[_, _], A, B]() extends FlowAST[Op, A ** B, B ** A]
  case class IntroFst[Op[_, _], A]() extends FlowAST[Op, A, Unit ** A]
  case class Prj1[Op[_, _], A, B]() extends FlowAST[Op, A ** B, A]
  case class Prj2[Op[_, _], A, B]() extends FlowAST[Op, A ** B, B]
  case class Dup[Op[_, _], A]() extends FlowAST[Op, A, A ** A]
  case class Either[Op[_, _], A, B, C](f: FlowAST[Op, A, C], g: FlowAST[Op, B, C]) extends FlowAST[Op, A ++ B, C]
  case class DistributeLR[Op[_, _], A, B, C]() extends FlowAST[Op, A ** (B ++ C), (A ** B) ++ (A ** C)]

  case class NewHttpReceptorEndpoint[Op[_, _], A]() extends FlowAST[Op, Unit, ReceptorEndpointDesc[A] ** A]

  case class DomainAction[Op[_, _], A, B](action: Op[A, B]) extends FlowAST[Op, A, B]

  given ssc[Op[_, _]]: SymmetricSemigroupalCategory[FlowAST[Op, _, _], **] with {
    override def id[A]: FlowAST[Op, A, A] = Id()
    override def andThen[A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]): FlowAST[Op, A, C] = AndThen(f, g)
    override def assocLR[A, B, C]: FlowAST[Op, (A ** B) ** C, A ** (B ** C)] = AssocLR()
    override def assocRL[A, B, C]: FlowAST[Op, A ** (B ** C), (A ** B) ** C] = AssocRL()
    override def par[A1, A2, B1, B2](f1: FlowAST[Op, A1, B1], f2: FlowAST[Op, A2, B2]): FlowAST[Op, A1 ** A2, B1 ** B2] = Par(f1, f2)
    override def swap[A, B]: FlowAST[Op, A ** B, B ** A] = Swap()
  }
}

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
      lambdas.absTopLevel(VarOrigin.LambdaAbstraction(pos), f) match {
        case Abstracted.Exact(g) => g.fold // TODO: should return "folded" already
        case Abstracted.Closure(x, g) => ???
        case Abstracted.Failure(e) => throw AssertionError(e)
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

    def newHttpReceptorEndpoint[A]: Flow[Unit, ReceptorEndpointDesc[A] ** A] =
      FlowAST.NewHttpReceptorEndpoint()

    def action[A, B](a: Action[A, B]): Flow[A, B] =
      FlowAST.DomainAction(a)

  }

  private val lambdas: Lambdas[Flow, **, VarOrigin] =
    Lambdas[Flow, **, VarOrigin](
      syntheticPairVar = (x, y) => VarOrigin.SyntheticPair(x, y),
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
      lambdas.switch[++, A ++ B, C](
        cases = {
          val left  = (VarOrigin.Left(pos))  -> ((c: LambdaContext) ?=> (a: Expr[A]) => f(Left(a)))
          val right = (VarOrigin.Right(pos)) -> ((c: LambdaContext) ?=> (b: Expr[B]) => f(Right(b)))
          Sink(Sink(left), Sink(right))
        },
        sum = [X, Y] => (f: Flow[X, C], g: Flow[Y, C]) => Flow.either(f, g),
        distribute = [X, Y, Z] => (_: Unit) => Flow.distributeLR[X, Y, Z],
      ) match {
        case Abstracted.Exact(g) => g(expr)
        case Abstracted.Closure(x, g) => lambdas.Expr.mapTupled(Tupled.zip(x, Tupled.atom(expr)), g)(VarOrigin.CapturingSwitch(pos))
        case Abstracted.Failure(e) => throw AssertionError(e)
      }

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
    case SyntheticPair(a: VarOrigin, b: VarOrigin)
