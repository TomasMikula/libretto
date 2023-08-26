package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.lang.*

type EmailAddress
type PersonalId
type EmploymentHistory
type CriminalRecord
type CivilRecord
type EmploymentVerificationResult
type Report

type CandidateResponse = Unit ++ (PersonalId ** EmploymentHistory)

enum Action[A, B]:
  case SendAcceptanceRequest extends Action[EmailAddress ** ReceptorEndpointDesc[CandidateResponse], Unit]
  case NotifyVerificationTeam extends Action[EmploymentHistory ** ReceptorEndpointDesc[EmploymentVerificationResult], Unit]
  case ReportCandidateDeclined extends Action[EmailAddress, Report]
  case CreateReport extends Action[CriminalRecord ** CivilRecord ** EmploymentVerificationResult, Report]
  case CheckCriminalRecord extends Action[PersonalId, CriminalRecord]
  case CheckCivilRecord extends Action[PersonalId, CivilRecord]

given workflows: Workflows[Action] = Workflows[Action]

export workflows.*

import workflows.Flow.{action, newHttpReceptorEndpoint}

def sendAcceptanceRequest: Flow[EmailAddress ** ReceptorEndpointDesc[CandidateResponse], Unit] =
  action(Action.SendAcceptanceRequest)

object Report {
  def candidateDeclined: Flow[EmailAddress, Report] =
    action(Action.ReportCandidateDeclined)

  def results: Flow[CriminalRecord ** CivilRecord ** EmploymentVerificationResult, Report] =
    action(Action.CreateReport)
}

def checkCriminalRecord: Flow[PersonalId, CriminalRecord] =
  action(Action.CheckCriminalRecord)

def checkCivilRecord: Flow[PersonalId, CivilRecord] =
  action(Action.CheckCivilRecord)

def notifyVerificationTeam: Flow[EmploymentHistory ** ReceptorEndpointDesc[EmploymentVerificationResult], Unit] =
  action(Action.NotifyVerificationTeam)