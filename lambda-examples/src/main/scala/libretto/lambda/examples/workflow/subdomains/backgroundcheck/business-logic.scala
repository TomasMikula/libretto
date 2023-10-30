package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.lang.{**, InputPortRef, Reading}
import workflows.Flow.{doWhile, injectL, injectR, read, readAwait, readAwaitTimeout}

import scala.concurrent.duration.*

val backgroundCheck: Flow[EmailAddress, Report] =
  Flow { candidate =>
    askForAcceptance(candidate) switch {
      case Left(_) =>
        Report.candidateDeclined(candidate)
      case Right(personalId ** employmentHistory) =>
        val criminalReport = checkCriminalRecord(personalId)
        val civilReport    = checkCivilRecord(personalId)
        val employmentCert = verifyEmploymentHistory(employmentHistory)
        Report.results(criminalReport ** civilReport ** employmentCert)
    }
  }

def askForAcceptance: Flow[EmailAddress, CandidateResponse] =
  Flow { emailAddr =>
    val inPort ** response = Expr(read[CandidateResponse])
    requestAcceptance(emailAddr ** inPort ** response)
  }

def requestAcceptance: Flow[EmailAddress ** InputPortRef[CandidateResponse] ** Reading[CandidateResponse], CandidateResponse] =
  doWhile { case addr ** due ** promised =>
    returning(
      readAwaitTimeout(1.day)(promised) switch {
        case Left(resp) => injectR(resp)
        case Right(p)   => injectL(addr ** due ** p)
      },
      sendAcceptanceRequest(addr ** due),
    )
  }

def verifyEmploymentHistory: Flow[EmploymentHistory, EmploymentVerificationResult] =
  Flow { history =>
    val inPort ** promised = Expr(read[EmploymentVerificationResult])
    returning(
      readAwait(promised),
      notifyVerificationTeam(history ** inPort),
    )
  }