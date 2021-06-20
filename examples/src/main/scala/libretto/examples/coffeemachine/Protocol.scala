package libretto.examples.coffeemachine

import libretto.StarterKit.dsl._

object Protocol {

  type CoffeeMachine = Rec[[CoffeeMachine] =>>
    (EspressoMenu |*| CoffeeMachine) |&|
    (LatteMenu    |*| CoffeeMachine) |&|
    Done
  ]

  type EspressoMenu =
    ShotCountChoice |*|
    Val[Beverage]       // `Val[A]` means a Scala value of type `A`
                        // flowing in the positive direction (left-to-right).
                        // Here it means that the coffee machine will *produce* a value of type Beverage.

  type LatteMenu =
    LatteOptions |*|
    Val[Beverage]

  type LatteOptions =
    SizeChoice      |*|
    ShotCountChoice |*|
    FlavorChoice

  // `Neg[A]` means a Scala value of type `A` flowing in the negative direction (right-to-left).
  // Here it means that the coffee machine is *asking for* input of type `A`.
  type ShotCountChoice = Neg[ShotCount]
  type SizeChoice      = Neg[Size]
  type FlavorChoice    = Neg[Option[Flavor]]

  enum ShotCount { case Single, Double       }
  enum Size      { case Small, Medium, Large }
  enum Flavor    { case Vanilla, Cinnamon    }

  case class Beverage(description: String)

  type LatteParams = (Size, ShotCount, Option[Flavor])

}
