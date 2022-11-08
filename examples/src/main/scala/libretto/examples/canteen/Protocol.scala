package libretto.examples.canteen

import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.$._

object Protocol {
  /** Interface of a canteen for one session.
    * The canteen facility is to the left of this interface,
    * whereas the customer is to the right.
    *
    * The session starts in the soup section.
    */
  opaque type Session = StageSoup
  object Session {
    def enter: Session -⚬ StageSoup =
      id

    def from[A](f: A -⚬ StageSoup): A -⚬ Session =
      f
  }

  /** At this stage, the customer has the option to get a soup or to move down the line to the next stage.
    * In fact, they may get multiple soups, but also no soup if there is none left.
    */
  type StageSoup = Rec[ [StageSoup] =>> // recursive types have to be defined using the `Rec` operator
    |&| [ // `|&|` means consumer choice: the party to the right (the "consumer", in our case the customer) chooses the branch

      // Option 1:
      //   Try to get a soup (if there's any left) and repeat this stage (to get an opportunity to get another soup).
      //   `|+|` means producer choice: the party to the left (the "producer", in our case the canteen facility) chooses the branch.
      //   Here, the facility chooses whether there is any soup left, or the customer has to proceed (without soup) to the next stage.
      (Soup |*| StageSoup) |+| StageMainDish,

      // Option 2:
      //   Proceed to the next stage.
      StageMainDish,
    ]
  ]

  object StageSoup {
    def from[A](
      onSoupRequest: A -⚬ ((Soup |*| StageSoup) |+| StageMainDish),
      goToNextStage: A -⚬ StageMainDish,
    ): A -⚬ StageSoup =
      λ { a => pack(choice(onSoupRequest, goToNextStage)(a)) }

    def getSoup: StageSoup -⚬ ((Soup |*| StageSoup) |+| StageMainDish) =
      unpack > chooseL

    def proceedToNextStage: StageSoup -⚬ StageMainDish =
      unpack > chooseR
  }

  /** At this stage, the customer has the option to get the main dish.
    * As with soup, the customer may get multiple main dishes. There's no variety though, to keep things simple.
    * At this stage, the customer no longer has the possibility to ask for soup, as they have moved to the next section of the canteen.
    */
  type StageMainDish = Rec[ [StageMainDish] =>>
    |&| [
      // Option 1: Try to get the main dish (if there's any left) and repeat this stage.
      (MainDish |*| StageMainDish) |+| StageDessert,

      // Option 2: Proceed to the next stage.
      StageDessert,
    ]
  ]

  object StageMainDish {
    def from[A](
      onDishRequest: A -⚬ ((MainDish |*| StageMainDish) |+| StageDessert),
      goToNextStage: A -⚬ StageDessert,
    ): A -⚬ StageMainDish =
      λ { a => pack(choice(onDishRequest, goToNextStage)(a)) }

    def getMainDish: StageMainDish -⚬ ((MainDish |*| StageMainDish) |+| StageDessert) =
      unpack > chooseL

    def proceedToNextStage: StageMainDish -⚬ StageDessert =
      unpack > chooseR
  }

  type StageDessert = Rec[ [StageDessert] =>>
    |&| [
      (Dessert |*| StageDessert) |+| StagePayment,
      StagePayment,
    ]
  ]

  object StageDessert {
    def from[A](
      onDessertRequest: A -⚬ ((Dessert |*| StageDessert) |+| StagePayment),
      goToNextStage:    A -⚬ StagePayment,
    ): A -⚬ StageDessert =
      λ { a => pack(choice(onDessertRequest, goToNextStage)(a)) }

    def getDessert: StageDessert -⚬ ((Dessert |*| StageDessert) |+| StagePayment) =
      unpack > chooseL

    def proceedToNextStage: StageDessert -⚬ StagePayment =
      unpack > chooseR
  }

  type StagePayment =
    PaymentCard =⚬ PaymentCard // The cashier borrows customer's payment card and always returns it back.

  type Soup     = Val["Soup"]
  type MainDish = Val["MainDish"]
  type Dessert  = Val["Dessert"]

  def eatSoup: Soup -⚬ Done =
    printLine(soup => s"Eating $soup")

  def eatMainDish: MainDish -⚬ Done =
    printLine(dish => s"Eating $dish")

  def eatDessert: Dessert -⚬ Done =
    printLine(dessert => s"Eating $dessert")

  opaque type PaymentCard = Val[String]

  object PaymentCard {
    def issue: Done -⚬ PaymentCard =
      constVal("1234 5678 9876 5432")

    def shred: PaymentCard -⚬ Done =
      neglect

    given SignalingJunction.Positive[PaymentCard] =
      signalingJunctionPositiveVal[String]
  }
}
