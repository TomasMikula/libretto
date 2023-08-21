package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.lang.*

type EmailAddress
type PersonalId
type EmploymentHistory
type CriminalRecord
type CivilRecord
type EmploymentVerificationResult
type Report

sealed trait Action[A, B]

val flow = Flows[Action]

export flow.{
  **,
  ++,
  Flow,
  Expr,
}

object Report {
  def candidateDeclined: Flow[EmailAddress, Report] =
    ???

  def results: Flow[CriminalRecord ** CivilRecord ** EmploymentVerificationResult, Report] =
    ???
}

def askForAcceptance: Flow[EmailAddress, Unit ++ (PersonalId ** EmploymentHistory)] =
  ???

def checkCriminalRecord: Flow[PersonalId, CriminalRecord] =
  ???

def checkCivilRecord: Flow[PersonalId, CivilRecord] =
  ???

def verifyEmploymentHistory: Flow[EmploymentHistory, EmploymentVerificationResult] =
  ???