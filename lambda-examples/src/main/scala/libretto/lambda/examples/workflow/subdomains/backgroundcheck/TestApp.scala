package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.runtime

object TestApp extends runtime.TestApp[Action, Val, EmailAddress, Report](
  DummyActionExecutor(_),
  emailAddress("john.doe@example.com"),
  backgroundCheck,
)
