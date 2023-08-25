package libretto.lambda.examples.workflow.generic.lang

import libretto.lambda.{Lambdas, SymmetricSemigroupalCategory}
import libretto.lambda.Lambdas.Abstracted
import libretto.lambda.util.{BiInjective, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl

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
  case class AndThen[Op[_, _], A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]) extends FlowAST[Op, A, C]

  case class NewHttpReceptorEndpoint[Op[_, _], A]() extends FlowAST[Op, Unit, ReceptorEndpointDesc[A] ** A]

  case class DomainAction[Op[_, _], A, B](action: Op[A, B]) extends FlowAST[Op, A, B]

  given ssc[Op[_, _]]: SymmetricSemigroupalCategory[FlowAST[Op, _, _], **] = ???
}

class Workflows[Action[_, _]] {
  import Workflows.VarOrigin

  object ** {
    def unapply[A, B](expr: Expr[A ** B]): (Expr[A], Expr[B]) =
      ???
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
        case Abstracted.Failure(e) => ???
      }

    def fst[A1, A2, B1](f: Flow[A1, B1]): Flow[A1 ** A2, B1 ** A2] =
      ???

    def introFst[X]: Flow[X, Unit ** X] =
      ???

    def introFst[X, A](f: Flow[Unit, A]): Flow[X, A ** X] =
      introFst[X] >>> fst(f)

    def elimSnd[X]: Flow[X ** Unit, X] =
      ???

    def newHttpReceptorEndpoint[A]: Flow[Unit, ReceptorEndpointDesc[A] ** A] =
      FlowAST.NewHttpReceptorEndpoint()

    def action[A, B](a: Action[A, B]): Flow[A, B] =
      FlowAST.DomainAction(a)

  }

  private val lambdas: Lambdas[Flow, **, VarOrigin] =
    Lambdas[Flow, **, VarOrigin]

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
    def **[B](b: Expr[B]): Expr[A ** B] =
      ???

  extension [A, B](expr: Expr[A ++ B])
    def switch[C](f: LambdaContext ?=> Either[Expr[A], Expr[B]] => Expr[C]): Expr[C] =
      ???

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
        case c :: cs => go(Flow.elimSnd(a ** c), cs)
    go(a, cmds.toList)
}

object Workflows:

  private[Workflows] enum VarOrigin:
    case LambdaAbstraction(pos: SourcePos)
    case FlowAppResult(pos: SourcePos)
    case ConstantExpr(pos: SourcePos)
