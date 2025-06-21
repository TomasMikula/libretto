package libretto.lambda.examples.workflow.subdomains.equipmentRequest

import libretto.lambda.examples.workflow.generic.lang.*
import libretto.lambda.examples.workflow.generic.runtime.{ActionExecutor, Value, WorkflowEngine}
import libretto.lambda.Items1Named.Member
import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.Indeed
import scala.util.{Success, Try}

class DummyActionExecutor(
  engine: WorkflowEngine[Activity, Val],
) extends ActionExecutor[Activity, Val] {

  override def submit[A, B](
    input: Value[Val, A],
    action: Activity[A, B],
  )(
    onComplete: Try[Value[Val, B]] => Unit,
  ): Unit = {
    val res: Value[Val, B] =
      action match {
        case Activity.RequestApproval =>
          summon[A =:= Request]
          summon[B =:= RejectionReason ++ Request]
          Value.right[Val, RejectionReason, Request](input)
        case Activity.RequestMonitorFromIT =>
          summon[A =:= DeskLocation]
          summon[B =:= Result]
          Value.ofEnum[Result]["Fulfilled"](Value.unit[Val])
        case Activity.RequestChairFromOfficeMgmt =>
          summon[A =:= DeskLocation]
          summon[B =:= Result]
          Value.ofEnum[Result]["FailedFulfillment"](
            Value.ofEnum[FulfillmentFailure]["OutOfStock"](Value.unit[Val])
          )
        case Activity.OrderFromSupplier =>
          summon[A =:= Equipment ** DeliveryAddress]
          summon[B =:= Result]
          val (equipment, addr) = Value.unpair(input: Value[Val, Equipment ** DeliveryAddress])
          val _: String = Value.extractString(addr)
          Value.revealCase(equipment) match
            case Indeed(Indeed(Value.Inject(i, a))) =>
              i match
                case Member.InLast(label) =>
                  summon[label.value.type <:< "Chair"]
                  summon[a.type <:< Value[Val, Unit]]
                  Value.ofEnum[Result]["FailedFulfillment"](
                    Value.ofEnum[FulfillmentFailure]["FailedDelivery"](Value.unit[Val])
                  )
                case Member.InInit(Member.Single(label)) =>
                  summon[label.value.type <:< "Monitor"]
                  summon[a.type <:< Value[Val, Unit]]
                  Value.ofEnum[Result]["Fulfilled"](Value.unit[Val])
      }

    onComplete(Success(res))
  }
}
