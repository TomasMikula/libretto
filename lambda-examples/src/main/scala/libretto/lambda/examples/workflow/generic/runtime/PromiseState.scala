package libretto.lambda.examples.workflow.generic.runtime

import scala.util.Try

enum PromiseState[Val[_], A]:
  case Empty()
  case Complete(result: Try[Value[Val, A]])
