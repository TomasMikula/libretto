package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic

enum Val[A]:
  case EmailAddr(value: String) extends Val[EmailAddress]

type Value[A] = generic.runtime.Value[Val, A]

def emailAddress(value: String): Value[EmailAddress] =
  generic.runtime.Value.Ext(Val.EmailAddr(value))
