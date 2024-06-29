package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.lang.{|| as |, *}
import workflows.Enum

type EmailAddress
type PersonalId
type EmploymentHistory
type CriminalRecord
type CivilRecord
type EmploymentVerificationResult
type Report

type CandidateResponse = Enum
  [ "Declined" :: Unit
  | "Accepted" :: (PersonalId ** EmploymentHistory)
  ]

object CandidateResponse:
  val Declined = Enum.partition[CandidateResponse]["Declined"]
  val Accepted = Enum.partition[CandidateResponse]["Accepted"]

enum Action[A, B]:
  case SendAcceptanceRequest extends Action[EmailAddress ** PortName[CandidateResponse], Unit]
  case NotifyVerificationTeam extends Action[EmploymentHistory ** PortName[EmploymentVerificationResult], Unit]
  case ReportCandidateDeclined extends Action[EmailAddress, Report]
  case CreateReport extends Action[CriminalRecord ** CivilRecord ** EmploymentVerificationResult, Report]
  case CheckCriminalRecord extends Action[PersonalId, CriminalRecord]
  case CheckCivilRecord extends Action[PersonalId, CivilRecord]

given workflows: Workflows[Action] = Workflows[Action]

export workflows.*

import workflows.Flow.action

def sendAcceptanceRequest: Flow[EmailAddress ** PortName[CandidateResponse], Unit] =
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

def notifyVerificationTeam: Flow[EmploymentHistory ** PortName[EmploymentVerificationResult], Unit] =
  action(Action.NotifyVerificationTeam)