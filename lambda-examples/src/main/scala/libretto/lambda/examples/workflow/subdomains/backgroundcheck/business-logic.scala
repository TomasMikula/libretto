package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.lang.{**, PortName, Reading}
import workflows.Flow.{doWhile, injectL, injectR, read, readAwait, readAwaitTimeout}

import scala.concurrent.duration.*

lazy val backgroundCheck: Flow[EmailAddress, Report] =
  Flow { candidate =>
    askForAcceptance(candidate) switch (
      is { case CandidateResponse.Declined(_) =>
        Report.candidateDeclined(candidate)
      },
      is { case CandidateResponse.Accepted(personalId ** employmentHistory) =>
        val criminalReport = checkCriminalRecord(personalId)
        val civilReport    = checkCivilRecord(personalId)
        val employmentCert = verifyEmploymentHistory(employmentHistory)
        Report.results(criminalReport ** civilReport ** employmentCert)
      },
    )
  }

def askForAcceptance: Flow[EmailAddress, CandidateResponse] =
  Flow { emailAddr =>
    val inPort ** response = Expr(read[CandidateResponse])
    requestAcceptance(emailAddr ** inPort ** response)
  }

def requestAcceptance: Flow[EmailAddress ** PortName[CandidateResponse] ** Reading[CandidateResponse], CandidateResponse] =
  doWhile { case addr ** due ** promised =>
    returning(
      readAwaitTimeout(1.day)(promised) switch (
        is { case InL(resp) => InR(resp) },
        is { case InR(p)    => InL(addr ** due ** p) },
      ),
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