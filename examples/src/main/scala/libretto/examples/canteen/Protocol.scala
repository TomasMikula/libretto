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
  opaque type Session = SectionSoup
  object Session {
    def enter: Session -⚬ SectionSoup =
      id

    def from[A](f: A -⚬ SectionSoup): A -⚬ Session =
      f
  }

  /** In this section, the customer has the option to get a soup or to move down the line to the next section.
    * In fact, they may get multiple soups, but also no soup if there is none left.
    */
  type SectionSoup = Rec[ [SectionSoup] =>> // recursive types have to be defined using the `Rec` operator
    |&| [ // `|&|` means consumer choice: the party to the right (the "consumer", in our case the customer) chooses the branch

      // Option 1:
      //   Try to get a soup (if there's any left) and remain in this section (to get an opportunity to get another soup).
      //   `|+|` means producer choice: the party to the left (the "producer", in our case the canteen facility) chooses the branch.
      //   Here, the facility chooses whether there is any soup left, or the customer has to proceed (without soup) to the next section.
      (Soup |*| SectionSoup) |+| SectionMainDish,

      // Option 2:
      //   Proceed to the next section.
      SectionMainDish,
    ]
  ]

  object SectionSoup {
    def from[A](
      onSoupRequest : A -⚬ ((Soup |*| SectionSoup) |+| SectionMainDish),
      goToMainDishes: A -⚬ SectionMainDish,
    ): A -⚬ SectionSoup =
      λ { a => pack(choice(onSoupRequest, goToMainDishes)(a)) }

    def getSoup: SectionSoup -⚬ ((Soup |*| SectionSoup) |+| SectionMainDish) =
      unpack > chooseL

    def proceedToMainDishes: SectionSoup -⚬ SectionMainDish =
      unpack > chooseR
  }

  /** In this section, the customer has the option to get the main dish.
    * As with soup, the customer may get multiple main dishes. There's no variety though, to keep things simple.
    * The customer no longer has the possibility to ask for soup, as they have already left the soup section.
    */
  type SectionMainDish = Rec[ [SectionMainDish] =>>
    |&| [
      // Option 1: Try to get the main dish (if there's any left) and remain in the main dish section.
      (MainDish |*| SectionMainDish) |+| SectionDessert,

      // Option 2: Proceed to the next section.
      SectionDessert,
    ]
  ]

  object SectionMainDish {
    def from[A](
      onDishRequest: A -⚬ ((MainDish |*| SectionMainDish) |+| SectionDessert),
      goToDesserts : A -⚬ SectionDessert,
    ): A -⚬ SectionMainDish =
      λ { a => pack(choice(onDishRequest, goToDesserts)(a)) }

    def getMainDish: SectionMainDish -⚬ ((MainDish |*| SectionMainDish) |+| SectionDessert) =
      unpack > chooseL

    def proceedToDesserts: SectionMainDish -⚬ SectionDessert =
      unpack > chooseR
  }

  type SectionDessert = Rec[ [SectionDessert] =>>
    |&| [
      (Dessert |*| SectionDessert) |+| SectionPayment,
      SectionPayment,
    ]
  ]

  object SectionDessert {
    def from[A](
      onDessertRequest: A -⚬ ((Dessert |*| SectionDessert) |+| SectionPayment),
      goToPayment     : A -⚬ SectionPayment,
    ): A -⚬ SectionDessert =
      λ { a => pack(choice(onDessertRequest, goToPayment)(a)) }

    def getDessert: SectionDessert -⚬ ((Dessert |*| SectionDessert) |+| SectionPayment) =
      unpack > chooseL

    def proceedToPayment: SectionDessert -⚬ SectionPayment =
      unpack > chooseR
  }

  type SectionPayment =
    PaymentCard =⚬ PaymentCard // The cashier borrows customer's payment card and always returns it back.

  opaque type Soup     = Val["Soup"]
  opaque type MainDish = Val["MainDish"]
  opaque type Dessert  = Val["Dessert"]

  def makeSoup: Done -⚬ Soup =
    printLine("Cooking soup") > constVal("Soup")

  def makeMainDish: Done -⚬ MainDish =
    printLine("Cooking main dish") > constVal("MainDish")

  def makeDessert: Done -⚬ Dessert =
    printLine("Cooking dessert") > constVal("Dessert")

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
