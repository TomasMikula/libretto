package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.lang.{**, Due, Promised}
import workflows.Flow.{doWhile, injectL, injectR, promiseAwait, promiseAwaitTimeout, promiseMake}

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
    val dueResponse ** response = Expr(promiseMake[CandidateResponse])
    requestAcceptance(emailAddr ** dueResponse ** response)
  }

def requestAcceptance: Flow[EmailAddress ** Due[CandidateResponse] ** Promised[CandidateResponse], CandidateResponse] =
  doWhile { case addr ** due ** promised =>
    returning(
      promiseAwaitTimeout(1.day)(promised) switch {
        case Left(resp) => injectR(resp)
        case Right(p)   => injectL(addr ** due ** p)
      },
      sendAcceptanceRequest(addr ** due),
    )
  }

def verifyEmploymentHistory: Flow[EmploymentHistory, EmploymentVerificationResult] =
  Flow { history =>
    val due ** promised = Expr(promiseMake[EmploymentVerificationResult])
    returning(
      promiseAwait(promised),
      notifyVerificationTeam(history ** due),
    )
  }