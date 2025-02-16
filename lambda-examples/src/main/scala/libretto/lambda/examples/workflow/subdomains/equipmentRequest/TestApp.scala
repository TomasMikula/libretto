package libretto.lambda.examples.workflow.subdomains.equipmentRequest

import libretto.lambda.examples.workflow.generic.runtime
import libretto.lambda.examples.workflow.generic.runtime.Value

object TestApp extends runtime.TestApp[Activity, Val, Request, Result](
  DummyActionExecutor(_),
  Value.ofEnum[Request]["WorkFromHome"](
    Value.Pair(
      Value.ofEnum[Equipment]["Monitor"](Value.unit[Val]),
      Value.string("43 Carrot Street, Gardenville, Veggie Republic")
    )
  ),
  equipmentRequest,
)
