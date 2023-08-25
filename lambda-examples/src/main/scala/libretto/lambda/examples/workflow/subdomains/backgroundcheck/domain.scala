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

given workflows: Workflows[Action] = Workflows[Action]

export workflows.*

import workflows.Flow.{action, newHttpReceptorEndpoint}

def sendAcceptanceRequest: Flow[EmailAddress ** ReceptorEndpointDesc[CandidateResponse], Unit] =
  action(Action.SendAcceptanceRequest)

object Report {
  def candidateDeclined: Flow[EmailAddress, Report] =
    ???

  def results: Flow[CriminalRecord ** CivilRecord ** EmploymentVerificationResult, Report] =
    ???
}

def checkCriminalRecord: Flow[PersonalId, CriminalRecord] =
  ???

def checkCivilRecord: Flow[PersonalId, CivilRecord] =
  ???

def verifyEmploymentHistory: Flow[EmploymentHistory, EmploymentVerificationResult] =
  ???