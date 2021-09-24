package libretto.examples.coffeemachine

import libretto.StarterKit.dsl
import libretto.StarterKit.dsl._

object Protocol {

  /** Interface between the coffee machine service (on the left) and client (on the right),
    * i.e. the service is the producer of this interface (`service: X -⚬ CoffeeMachine`),
    * whereas the client is the consumer of this interface (`client: CoffeeMachine -⚬ Y`).
    *
    * The service offers the client a choice (`|&|`) between espresso, latte, and ending the interaction.
    */
  opaque type CoffeeMachine = Rec[[CoffeeMachine] =>>
    // When the client chooses espresso, they have to provide the options to tweak their espresso (`ExpressoOptions`)
    // and in return get a beverage, as well as the next round of interaction with the machine (`CoffeeMachine`).
    (EspressoOptions =⚬ (Val[Beverage] |*| CoffeeMachine)) |&|

    // Similarly, when the client chooses latte, they have to provide `LatteOptions` and
    // in return get a beverage, as well as the next round of interaction with the machine.
    (LatteOptions =⚬ (Val[Beverage] |*| CoffeeMachine)) |&|

    // This choice means the end of interaction with the machine.
    Done
  ]

  object CoffeeMachine {
    /** Hides one level of recursive definition of CoffeeMachine.
      * It is just `dsl.pack` applied to a type argument, in order to help type inference.
      */
    private def pack: ((EspressoOptions =⚬ (Val[Beverage] |*| CoffeeMachine)) |&| (LatteOptions =⚬ (Val[Beverage] |*| CoffeeMachine)) |&| Done) -⚬ CoffeeMachine =
      dsl.pack[[x] =>> (EspressoOptions =⚬ (Val[Beverage] |*| x)) |&| (LatteOptions =⚬ (Val[Beverage] |*| x)) |&| Done]

    /** Unwraps one level of recursive definition of CoffeeMachine.
      * It is just `dsl.unpack` specialized for `CoffeeMachine`, in order to help type inference.
      */
    private def unpack: CoffeeMachine -⚬ ((EspressoOptions =⚬ (Val[Beverage] |*| CoffeeMachine)) |&| (LatteOptions =⚬ (Val[Beverage] |*| CoffeeMachine)) |&| Done) =
      dsl.unpack

    /** Constructor */
    def create(
      espresso: Done -⚬ (EspressoOptions =⚬ (Val[Beverage] |*| CoffeeMachine)),
      latte:    Done -⚬ (LatteOptions =⚬ (Val[Beverage] |*| CoffeeMachine)),
    ): Done -⚬ CoffeeMachine =
      choice(
        choice(espresso, latte),
        id[Done],
      ) > pack

    /***************
     * Destructors *
     ***************/

    def chooseEspresso: CoffeeMachine -⚬ (EspressoOptions =⚬ (Val[Beverage] |*| CoffeeMachine)) =
      unpack > chooseL > chooseL

    def chooseLatte: CoffeeMachine -⚬ (LatteOptions =⚬ (Val[Beverage] |*| CoffeeMachine)) =
      unpack > chooseL > chooseR

    def chooseQuit: CoffeeMachine -⚬ Done =
      unpack > chooseR
  }

  type EspressoOptions =
    Val[ShotCount]

  type LatteOptions =
    Val[Size]           |*|
    Val[ShotCount]      |*|
    Val[Option[Flavor]]

  enum ShotCount { case Single, Double       }
  enum Size      { case Small, Medium, Large }
  enum Flavor    { case Vanilla, Cinnamon    }

  case class Beverage(description: String)

}
