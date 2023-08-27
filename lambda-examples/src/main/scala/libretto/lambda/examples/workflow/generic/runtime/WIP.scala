package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.Capture
import libretto.lambda.examples.workflow.generic.lang.{**, FlowAST}

sealed trait WIP[Action[_, _], Val[_], A] {
  import WIP.*

  def isActive: Boolean =
    this match {
      case _: Still[Action, Val, A] => false
      case Zip(_, _) => true
      case Map(_, _) => true
    }

  def resultOpt: Option[WorkflowResult[Val, A]] =
    this match
      case Done(value) => Some(WorkflowResult.Success(value))
      case Zip(a1, a2) => None
      case Map(a, f) => None

}

object WIP {
  enum PartiallyAppliedAction[Action[_, _], Val[_], A, B]:
    case Impl[Action[_, _], Val[_], A, X, B](
      args: Capture[**, Val, A, X],
      f: Action[X, B],
    ) extends PartiallyAppliedAction[Action, Val, A, B]

  object PartiallyAppliedAction {
    def pure[Action[_, _], Val[_], A, B](f: Action[A, B]): PartiallyAppliedAction[Action, Val, A, B] =
      PartiallyAppliedAction.Impl(Capture.NoCapture(), f)
  }

  type Closure[Action[_, _], Val[_], A, B] = FlowAST[PartiallyAppliedAction[Action, Val, _, _], A, B]
  object Closure {
    def pure[Action[_, _], Val[_], A, B](f: FlowAST[Action, A, B]): Closure[Action, Val, A, B] =
      f.translate([x, y] => (f: Action[x, y]) => PartiallyAppliedAction.pure[Action, Val, x, y](f))
  }

  case class Zip[Action[_, _], Val[_], A1, A2](a1: WIP[Action, Val, A1], a2: WIP[Action, Val, A2]) extends WIP[Action, Val, A1 ** A2]
  case class Map[Action[_, _], Val[_], A, B](a: WIP[Action, Val, A], f: Closure[Action, Val, A, B]) extends WIP[Action, Val, B]

  sealed trait Still[Action[_, _], Val[_], A] extends WIP[Action, Val, A]
  case class Done[Action[_, _], Val[_], A](value: Value[Val, A]) extends Still[Action, Val, A]

  def init[Action[_, _], Val[_], A, B](
    input: Value[Val, A],
    wf: FlowAST[Action, A, B],
  ): WIP[Action, Val, B] =
    Map(Done(input), Closure.pure(wf))
}
