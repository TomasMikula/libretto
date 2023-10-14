package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.lang.{**, PromiseRef}
import workflows.Flow.{delay, doWhile, injectL, injectR, isComplete, promise}

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
    val responseEndpoint ** response = Expr(promise[CandidateResponse])
    returning(
      response,
      sendAcceptanceRequest(emailAddr ** responseEndpoint),
    )
  }

def requestAcceptance: Flow[EmailAddress ** PromiseRef[CandidateResponse], Unit] =
  doWhile { case addr ** ref =>
    returning(
      switch (isComplete(delay(1.day)(ref))) {
        case Left(_) => injectL(addr ** ref)
        case Right(_)  => injectR(unit)
      },
      sendAcceptanceRequest(addr ** ref),
    )
  }

def verifyEmploymentHistory: Flow[EmploymentHistory, EmploymentVerificationResult] =
  Flow { history =>
    val responseEndpoint ** response = Expr(promise[EmploymentVerificationResult])
    returning(
      response,
      notifyVerificationTeam(history ** responseEndpoint),
    )
  }