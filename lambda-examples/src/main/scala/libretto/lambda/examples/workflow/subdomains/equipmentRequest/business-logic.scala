package libretto.lambda.examples.workflow.subdomains.equipmentRequest

import Activity.*
import Equipment.*
import Request.*

def equipmentRequest: Flow[Request, Result] =
  Flow { req =>
    req switch (
      is { case ForOffice(Monitor(_) ** deskLocation) =>
        requestMonitorFromIT(deskLocation)
      },
      is { case ForOffice(Chair(_) ** deskLocation) =>
        requestChairFromOfficeMgmt(deskLocation)
      },
      is { case WorkFromHome(item ** address) =>
        orderFromSupplier(item ** address)
      },
    )
  }
