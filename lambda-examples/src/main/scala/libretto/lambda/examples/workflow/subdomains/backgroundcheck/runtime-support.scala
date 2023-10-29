package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.Unzippable
import libretto.lambda.examples.workflow.generic
import libretto.lambda.examples.workflow.generic.lang.**

enum Val[A]:
  case EmailAddr(value: String) extends Val[EmailAddress]
  case PersonId(value: String) extends Val[PersonalId]
  case EmployHistory(value: String) extends Val[EmploymentHistory]
  case VerificationResult(value: Boolean) extends Val[EmploymentVerificationResult]
  case CrimiRec(clean: Boolean) extends Val[CriminalRecord]
  case CivilRec(clean: Boolean) extends Val[CivilRecord]

object Val:
  given Unzippable[**, Val] with
    override def unzip[A, B](x: Val[A ** B]): (Val[A], Val[B]) =
      throw new AssertionError(s"Unexpected value representing pair: $x")

type Value[A] = generic.runtime.Value[Val, A]

def emailAddress(value: String): Value[EmailAddress] =
  generic.runtime.Value.Ext(Val.EmailAddr(value))

def personalId(value: String): Value[PersonalId] =
  generic.runtime.Value.Ext(Val.PersonId(value))

def employmentHistory(value: String): Value[EmploymentHistory] =
  generic.runtime.Value.Ext(Val.EmployHistory(value))

def employmentVerificationResult(value: Boolean): Value[EmploymentVerificationResult] =
  generic.runtime.Value.Ext(Val.VerificationResult(value))

def criminalRecord(clean: Boolean): Value[CriminalRecord] =
  generic.runtime.Value.Ext(Val.CrimiRec(clean))

def civilRecord(clean: Boolean): Value[CivilRecord] =
  generic.runtime.Value.Ext(Val.CivilRec(clean))
