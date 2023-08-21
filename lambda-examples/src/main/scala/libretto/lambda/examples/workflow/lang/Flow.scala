package libretto.lambda.examples.workflow.lang

import libretto.lambda.{Lambdas, SymmetricSemigroupalCategory}
import libretto.lambda.Lambdas.Abstracted
import libretto.lambda.util.{BiInjective, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl

class Flows[Action[_, _]] {
  import Flows.VarOrigin

  /** A domain-level pair.
    *
    * Uninhabited, used only as a (phantom) type index.
    */
  sealed trait **[A, B]

  object ** {
    def unapply[A, B](expr: Expr[A ** B]): (Expr[A], Expr[B]) =
      ???

    given BiInjective[**] with {
      override def unapply[A, B, X, Y](ev: A ** B =:= X ** Y): (A =:= X, B =:= Y) =
        ev match { case TypeEq(Refl()) => (summon, summon) }
    }
  }

  /** A domain-level `Either`.
    *
    * Uninhabited, used only as a (phantom) type index.
    */
  sealed trait ++[A, B]

  sealed trait Flow[A, B] {
    def apply(using pos: SourcePos)(a: Expr[A])(using LambdaContext): Expr[B] =
      lambdas.Expr.map(a, this)(VarOrigin.FlowAppResult(pos))
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

    given SymmetricSemigroupalCategory[Flow, **] = ???

  }

  private val lambdas: Lambdas[Flow, **, VarOrigin] =
    Lambdas[Flow, **, VarOrigin]

  opaque type Expr[A]       = lambdas.Expr[A]
  opaque type LambdaContext = lambdas.Context

  extension [A](a: Expr[A])
    def **[B](b: Expr[B]): Expr[A ** B] =
      ???

  extension [A, B](expr: Expr[A ++ B])
    def switch[C](f: LambdaContext ?=> Either[Expr[A], Expr[B]] => Expr[C]): Expr[C] =
      ???
}

object Flows:

  private[Flows] enum VarOrigin:
    case LambdaAbstraction(pos: SourcePos)
    case FlowAppResult(pos: SourcePos)
