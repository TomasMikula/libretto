package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.lang.{**, PortName}
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
        notifyVerificationTeam(input, onComplete)
      case Action.ReportCandidateDeclined =>
        UnhandledCase.raise(s"ActionExecutor#executeAction($action)")
      case Action.CreateReport =>
        createReport(input, onComplete)
      case Action.CheckCriminalRecord =>
        checkCriminalRecord(input, onComplete)
      case Action.CheckCivilRecord =>
        checkCivilRecord(input, onComplete)

  private def sendAcceptanceRequest(
    args: Value[Val, EmailAddress ** PortName[CandidateResponse]],
    onComplete: Try[Value[Val, Unit]] => Unit,
  ): Unit =
    val (addr, promResp) = Value.unpair(args)
    promResp match
      case Value.PortNameValue(p) =>
        val pId: Value[Val, PersonalId] =
          personalId("1234")
        val hist: Value[Val, EmploymentHistory] =
          employmentHistory("Facebook, Microsoft, Amazon")
        engine.completeReading(p, Success(Value.right(pId ** hist)))
        onComplete(Success(Value.unit))
      case other =>
        throw AssertionError(s"Unexpected value of type InputPortRef[T]: $other")

  private def notifyVerificationTeam(
    args: Value[Val, EmploymentHistory ** PortName[EmploymentVerificationResult]],
    onComplete: Try[Value[Val, Unit]] => Unit,
  ): Unit =
    val (hist, ref) = Value.unpair(args)
    ref match
      case Value.PortNameValue(ref) =>
        val res: Value[Val, EmploymentVerificationResult] =
          employmentVerificationResult(true)
        engine.completeReading(ref, Success(res))
        onComplete(Success(Value.unit))
      case other =>
        throw AssertionError(s"Unexpected value of type InputPortRef[T]: $other")

  private def checkCriminalRecord(
    args: Value[Val, PersonalId],
    onComplete: Try[Value[Val, CriminalRecord]] => Unit,
  ): Unit =
    args match
      case Value.Ext(Val.PersonId(personalId)) =>
        onComplete(Success(criminalRecord(clean = true)))
      case other =>
        throw AssertionError(s"Unexpected value of type PersonalId: $other")

  private def checkCivilRecord(
    args: Value[Val, PersonalId],
    onComplete: Try[Value[Val, CivilRecord]] => Unit,
  ): Unit =
    args match
      case Value.Ext(Val.PersonId(personalId)) =>
        onComplete(Success(civilRecord(clean = true)))
      case other =>
        throw AssertionError(s"Unexpected value of type PersonalId: $other")

  private def createReport(
    args: Value[Val, CriminalRecord ** CivilRecord ** EmploymentVerificationResult],
    onComplete: Try[Value[Val, Report]] => Unit,
  ): Unit =
    val (records, verification) = Value.unpair(args)
    val (crimiRec, civilRec)    = Value.unpair(records)
    val report = makeReport(crimiRec, civilRec, verification)
    onComplete(Success(report))
}
