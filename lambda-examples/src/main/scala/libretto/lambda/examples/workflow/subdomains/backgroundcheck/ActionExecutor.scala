package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.runtime.{Value, Worker}
import libretto.lambda.UnhandledCase
import scala.util.Try

class ActionExecutor extends Worker[Action, Val] {
  override def executeAction[A, B](
    input: Value[Val, A],
    action: Action[A, B],
  )(
    onComplete: Try[Value[Val, B]] => Unit,
  ): Unit =
    action match
      case Action.SendAcceptanceRequest =>
        UnhandledCase.raise(s"ActionExecutor#executeAction($action)")
      case Action.NotifyVerificationTeam =>
        UnhandledCase.raise(s"ActionExecutor#executeAction($action)")
      case Action.ReportCandidateDeclined =>
        UnhandledCase.raise(s"ActionExecutor#executeAction($action)")
      case Action.CreateReport =>
        UnhandledCase.raise(s"ActionExecutor#executeAction($action)")
      case Action.CheckCriminalRecord =>
        UnhandledCase.raise(s"ActionExecutor#executeAction($action)")
      case Action.CheckCivilRecord =>
        UnhandledCase.raise(s"ActionExecutor#executeAction($action)")

}
