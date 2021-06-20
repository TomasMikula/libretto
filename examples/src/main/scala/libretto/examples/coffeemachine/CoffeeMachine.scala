package libretto.examples.coffeemachine

import libretto.StarterApp

object CoffeeMachine extends StarterApp { app =>

  override def blueprint: Done -⚬ Done =
    CoffeeMachineProvider.makeCoffeeMachine > CoffeeMachineClient.useCoffeeMachine

}
