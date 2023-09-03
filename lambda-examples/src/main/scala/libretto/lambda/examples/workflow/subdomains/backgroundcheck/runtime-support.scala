package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.Unzippable
import libretto.lambda.examples.workflow.generic
import libretto.lambda.examples.workflow.generic.lang.**

enum Val[A]:
  case EmailAddr(value: String) extends Val[EmailAddress]

object Val:
  given Unzippable[**, Val] with
    override def unzip[A, B](x: Val[A ** B]): (Val[A], Val[B]) =
      x match
        case Val.EmailAddr(_) => throw new AssertionError("impossible")

type Value[A] = generic.runtime.Value[Val, A]

def emailAddress(value: String): Value[EmailAddress] =
  generic.runtime.Value.Ext(Val.EmailAddr(value))
