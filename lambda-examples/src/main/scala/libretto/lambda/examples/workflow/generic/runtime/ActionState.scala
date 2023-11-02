package libretto.lambda.examples.workflow.generic.runtime

import scala.util.Try

enum ActionState[Val[_], A]:
  case Empty()
  case Completed(result: Try[Value[Val, A]])
