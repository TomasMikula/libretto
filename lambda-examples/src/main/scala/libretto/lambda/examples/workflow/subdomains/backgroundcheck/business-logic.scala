package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import workflows.Flow.newHttpReceptorEndpoint

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
    val responseEndpoint ** response = Expr(newHttpReceptorEndpoint[CandidateResponse])
    returning(
      response,
      sendAcceptanceRequest(emailAddr ** responseEndpoint),
    )
  }

def verifyEmploymentHistory: Flow[EmploymentHistory, EmploymentVerificationResult] =
  Flow { history =>
    val responseEndpoint ** response = Expr(newHttpReceptorEndpoint[EmploymentVerificationResult])
    returning(
      response,
      notifyVerificationTeam(history ** responseEndpoint),
    )
  }