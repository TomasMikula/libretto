package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.Unzippable
import libretto.lambda.examples.workflow.generic
import libretto.lambda.examples.workflow.generic.lang.{**, ++, Enum, Reading}
import libretto.lambda.examples.workflow.generic.runtime.{PortId, Value}
import libretto.lambda.examples.workflow.generic.runtime.Value.Ext
import libretto.lambda.util.Exists

enum Val[A]:
  case EmailAddr(value: String) extends Val[EmailAddress]
  case PersonId(value: String) extends Val[PersonalId]
  case EmployHistory(value: String) extends Val[EmploymentHistory]
  case VerificationResult(value: Boolean) extends Val[EmploymentVerificationResult]
  case CrimiRec(clean: Boolean) extends Val[CriminalRecord]
  case CivilRec(clean: Boolean) extends Val[CivilRecord]
  case ReportResults(
    crimiClean: Boolean,
    civilClean: Boolean,
    employmentHistoryChecksUp: Boolean,
  ) extends Val[Report]

object Val:
  given Value.Compliant[Val] with
    override def unzip[A, B](x: Val[A ** B]): (Val[A], Val[B]) =
      throw new AssertionError(s"Unexpected value representing a pair (`**`): $x")
    override def toEither[A, B](value: Val[A ++ B]): Either[Val[A], Val[B]] =
      throw new AssertionError(s"Unexpected value representing `++`: $value")
    override def extractPortId[A](value: Val[Reading[A]]): PortId[A] =
      throw new AssertionError(s"Unexpected value representing input port (`Reading[A]`): $value")
    override def revealCase[Cases](value: Val[Enum[Cases]]): Exists[[Lbl] =>> Exists[[A] =>> Value.Inject[Val, Lbl, A, Cases]]] =
      throw new AssertionError(s"Unexpected value representing `Enum`: $value")

type Value[A] = generic.runtime.Value[Val, A]

def emailAddress(value: String): Value[EmailAddress] =
  Ext(Val.EmailAddr(value))

def personalId(value: String): Value[PersonalId] =
  Ext(Val.PersonId(value))

def employmentHistory(value: String): Value[EmploymentHistory] =
  Ext(Val.EmployHistory(value))

def employmentVerificationResult(value: Boolean): Value[EmploymentVerificationResult] =
  Ext(Val.VerificationResult(value))

def criminalRecord(clean: Boolean): Value[CriminalRecord] =
  Ext(Val.CrimiRec(clean))

def civilRecord(clean: Boolean): Value[CivilRecord] =
  Ext(Val.CivilRec(clean))

def makeReport(
  crimiRecord: Value[CriminalRecord],
  civilRecord: Value[CivilRecord],
  verification: Value[EmploymentVerificationResult],
): Value[Report] =
  val crimiClean = crimiRecord match
    case Ext(Val.CrimiRec(value)) => value
  val civilClean = civilRecord match
    case Ext(Val.CivilRec(value)) => value
  val verified = verification match
    case Ext(Val.VerificationResult(value)) => value
  generic.runtime.Value.Ext(
    Val.ReportResults(crimiClean, civilClean, verified)
  )
