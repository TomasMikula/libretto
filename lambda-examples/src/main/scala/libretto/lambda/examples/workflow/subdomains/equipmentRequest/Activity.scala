package libretto.lambda.examples.workflow.subdomains.equipmentRequest

import libretto.lambda.examples.workflow.generic.lang.*

enum Activity[A, B]:
  case RequestMonitorFromIT       extends Activity[DeskLocation, Result]
  case RequestChairFromOfficeMgmt extends Activity[DeskLocation, Result]
  case OrderFromSupplier          extends Activity[Equipment ** DeliveryAddress, Result]

object Activity:
  def requestMonitorFromIT: Flow[DeskLocation, Result] =
    Flow.action(RequestMonitorFromIT)

  def requestChairFromOfficeMgmt: Flow[DeskLocation, Result] =
    Flow.action(RequestChairFromOfficeMgmt)

  def orderFromSupplier: Flow[Equipment ** DeliveryAddress, Result] =
    Flow.action(OrderFromSupplier)
