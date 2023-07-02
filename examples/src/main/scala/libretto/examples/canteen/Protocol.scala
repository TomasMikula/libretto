package libretto.examples.canteen

import libretto.scaletto.StarterKit.*
import libretto.scaletto.StarterKit.$.*
import libretto.scaletto.StarterKit.scalettoLib.given

object Protocol {
  /** Interface of a canteen for one session.
    * The canteen facility is to the left of this interface,
    * whereas the customer is to the right.
    *
    * The session starts in the soup section.
    */
  opaque type Session = SectionSoup
  object Session {
    def proceedToSoups: Session -⚬ SectionSoup =
      id

    def create: SectionSoup -⚬ Session =
      id
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
      (Soup |*| SectionSoup) |+| SectionMain,

      // Option 2:
      //   Proceed to the next section.
      SectionMain,
    ]
  ]

  object SectionSoup {
    private def pack: (((Soup |*| SectionSoup) |+| SectionMain) |&| SectionMain) -⚬ SectionSoup =
      dsl.pack[[S] =>> ((Soup |*| S) |+| SectionMain) |&| SectionMain]

    def from[A](
      onSoupRequest : A -⚬ ((Soup |*| SectionSoup) |+| SectionMain),
      goToMainDishes: A -⚬ SectionMain,
    ): A -⚬ SectionSoup =
      choice(onSoupRequest, goToMainDishes) > pack

    def getSoup: SectionSoup -⚬ ((Soup |*| SectionSoup) |+| SectionMain) =
      unpack > chooseL

    def proceedToMainDishes: SectionSoup -⚬ SectionMain =
      unpack > chooseR
  }

  /** In this section, the customer has the option to get the main dish.
    * As with soup, the customer may get multiple main dishes. There's no variety though, to keep things simple.
    * The customer no longer has the possibility to ask for soup, as they have already left the soup section.
    */
  type SectionMain = Rec[ [SectionMain] =>>
    |&| [
      // Option 1: Try to get the main dish (if there's any left).
      // If successful, remain in the main dish section, otherwise, proceed to the payment section.
      (MainDish |*| SectionMain) |+| SectionPayment,

      // Option 2: Proceed to the payment section.
      SectionPayment,
    ]
  ]

  object SectionMain {
    def from[A](
      onDishRequest: A -⚬ ((MainDish |*| SectionMain) |+| SectionPayment),
      goToPayment  : A -⚬ SectionPayment,
    ): A -⚬ SectionMain =
      λ { a => pack(choice(onDishRequest, goToPayment)(a)) }

    def getMainDish: SectionMain -⚬ ((MainDish |*| SectionMain) |+| SectionPayment) =
      unpack > chooseL

    def proceedToPayment: SectionMain -⚬ SectionPayment =
      unpack > chooseR
  }

  type SectionPayment =
    PaymentCard =⚬ PaymentCard // The cashier borrows customer's payment card and always returns it back.

  opaque type Soup     = Val["Soup"]
  opaque type MainDish = Val["MainDish"]

  def makeSoup: Done -⚬ Soup =
    printLine("Cooking soup") > constVal("Soup")

  def makeMainDish: Done -⚬ MainDish =
    printLine("Cooking main dish") > constVal("MainDish")

  def eatSoup: Soup -⚬ Done =
    printLine(soup => s"Eating $soup")

  def eatMainDish: MainDish -⚬ Done =
    printLine(dish => s"Eating $dish")

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
