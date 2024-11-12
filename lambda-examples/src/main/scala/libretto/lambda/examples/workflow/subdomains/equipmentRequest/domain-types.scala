package libretto.lambda.examples.workflow.subdomains.equipmentRequest

import libretto.lambda.examples.workflow.generic.lang.{|| as |, *}

type Request = Enum
  [ "ForOffice" :: (Equipment ** DeskLocation)
  | "WorkFromHome" :: (Equipment ** DeliveryAddress)
  ]

object Request:
  val ForOffice    = Enum.partition[Request]["ForOffice"]
  val WorkFromHome = Enum.partition[Request]["WorkFromHome"]

type Equipment = Enum
  [ "Monitor" :: Unit
  | "Chair" :: Unit
  ]

object Equipment:
  val Monitor = Enum.partition[Equipment]["Monitor"]
  val Chair   = Enum.partition[Equipment]["Chair"]

type DeskLocation
type DeliveryAddress

type Result = Enum
  [ "Declined" :: RejectionReason
  | "FailedFulfillment" :: FulfillmentFailure
  | "Fulfilled" :: Unit
  ]

object Result:
  val Declined          = Enum.partition[Result]["Declined"]
  val FailedFulfillment = Enum.partition[Result]["Declined"]
  val Fulfilled         = Enum.partition[Result]["Declined"]

type RejectionReason = Enum
  [ "ManagerDeclined" :: Unit
  | "NoBudget" :: Unit
  ]

type FulfillmentFailure = Enum
  [ "FailedDelivery" :: Unit
  | "OutOfStock" :: Unit
  ]
