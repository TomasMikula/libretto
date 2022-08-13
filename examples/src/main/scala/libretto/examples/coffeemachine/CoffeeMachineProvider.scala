package libretto.examples.coffeemachine

import libretto.scaletto.StarterKit
import libretto.scaletto.StarterKit._

object CoffeeMachineProvider {
  import Protocol._
  import $._

  val makeCoffeeMachine: Done -⚬ CoffeeMachine = rec { self =>
    val returnAndRepeat: Val[Beverage] -⚬ (Val[Beverage] |*| CoffeeMachine) =
      signalDone >
        λ { case (beverage |*| beverageDone) =>
          val nextMachine: $[CoffeeMachine] = when(beverageDone) { self }
          beverage |*| nextMachine
        }

    CoffeeMachine.create(
      serveEspresso > out(returnAndRepeat),
      serveLatte    > out(returnAndRepeat),
    )
  }

  private def serveEspresso: Done -⚬ (EspressoOptions =⚬ Val[Beverage]) =
    λ { ready =>
      Λ { espressoOptions =>
        (espressoOptions waitFor ready) > makeEspresso
      }
    }

  private def serveLatte: Done -⚬ (LatteOptions =⚬ Val[Beverage]) =
    λ { ready =>
      Λ { latteOptions =>
        (latteSpec(latteOptions) waitFor ready) > makeLatte
      }
    }

  private type LatteSpec = (Size, ShotCount, Option[Flavor])

  private def makeEspresso: EspressoOptions -⚬ Val[Beverage] =
    mapVal(espresso)

  private def makeLatte: Val[LatteSpec] -⚬ Val[Beverage] =
    mapVal(latte)

  private def latteSpec: LatteOptions -⚬ Val[LatteSpec] =
    λ { case size |*| shotCount |*| flavor =>
      unliftPair(unliftPair(size |*| shotCount) |*| flavor) > mapVal {
        case ((a, b), c) => (a, b, c)
      }
    }

  private def espresso(shots: ShotCount): Beverage =
    Beverage("Espresso" + (shots match {
      case ShotCount.Double => " doppio"
      case ShotCount.Single => ""
    }))

  private def latte(params: LatteSpec): Beverage = {
    val (size, shots, flavor) = params
    val flavorStr = flavor.map(_.toString.toLowerCase + " ").getOrElse("")
    val shotsStr = shots match {
      case ShotCount.Double => " with an extra shot"
      case ShotCount.Single => ""
    }
    Beverage(s"$size ${flavorStr}latte$shotsStr")
  }
}
