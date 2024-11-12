package libretto.lambda.examples.workflow.subdomains.equipmentRequest

import libretto.lambda.examples.workflow.generic.lang.*

enum Activity[A, B]:
  case RequestApproval            extends Activity[Request, RejectionReason ++ Request]
  case RequestMonitorFromIT       extends Activity[DeskLocation, Result]
  case RequestChairFromOfficeMgmt extends Activity[DeskLocation, Result]
  case OrderFromSupplier          extends Activity[Equipment ** DeliveryAddress, Result]

object Activity:
  def requestApproval: Flow[Request, RejectionReason ++ Request] =
    Flow.action(RequestApproval)

  def requestMonitorFromIT: Flow[DeskLocation, Result] =
    Flow.action(RequestMonitorFromIT)

  def requestChairFromOfficeMgmt: Flow[DeskLocation, Result] =
    Flow.action(RequestChairFromOfficeMgmt)

  def orderFromSupplier: Flow[Equipment ** DeliveryAddress, Result] =
    Flow.action(OrderFromSupplier)
