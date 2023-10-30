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
  case SendAcceptanceRequest extends Action[EmailAddress ** InputPortRef[CandidateResponse], Unit]
  case NotifyVerificationTeam extends Action[EmploymentHistory ** InputPortRef[EmploymentVerificationResult], Unit]
  case ReportCandidateDeclined extends Action[EmailAddress, Report]
  case CreateReport extends Action[CriminalRecord ** CivilRecord ** EmploymentVerificationResult, Report]
  case CheckCriminalRecord extends Action[PersonalId, CriminalRecord]
  case CheckCivilRecord extends Action[PersonalId, CivilRecord]

given workflows: Workflows[Action] = Workflows[Action]

export workflows.*

import workflows.Flow.action

def sendAcceptanceRequest: Flow[EmailAddress ** InputPortRef[CandidateResponse], Unit] =
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

def notifyVerificationTeam: Flow[EmploymentHistory ** InputPortRef[EmploymentVerificationResult], Unit] =
  action(Action.NotifyVerificationTeam)