package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.lang.{**, PromiseRef}
import libretto.lambda.examples.workflow.generic.runtime.{ActionExecutor, Value, WorkflowEngine}
import libretto.lambda.UnhandledCase
import scala.util.{Success, Try}

class DummyActionExecutor(
  engine: WorkflowEngine[Action, Val],
) extends ActionExecutor[Action, Val] {
  override def submit[A, B](
    input: Value[Val, A],
    action: Action[A, B],
  )(
    onComplete: Try[Value[Val, B]] => Unit,
  ): Unit =
    action match
      case Action.SendAcceptanceRequest =>
        sendAcceptanceRequest(input, onComplete)
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

  private def sendAcceptanceRequest(
    args: Value[Val, EmailAddress ** PromiseRef[CandidateResponse]],
    onComplete: Try[Value[Val, Unit]] => Unit,
  ): Unit =
    val (addr, promResp) = Value.unpair(args)
    promResp match
      case Value.PromiseToComplete(p) =>
        val pId: Value[Val, PersonalId] =
          personalId("1234")
        val hist: Value[Val, EmploymentHistory] =
          employmentHistory("Facebook, Microsoft, Amazon")
        engine.completePromise(p, Success(Value.right(pId ** hist)))
        onComplete(Success(Value.unit))
      case other =>
        throw AssertionError(s"Unexpected value of type PromiseRef: $other")
}
