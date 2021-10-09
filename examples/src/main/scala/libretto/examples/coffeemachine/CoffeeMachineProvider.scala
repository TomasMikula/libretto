package libretto.examples.coffeemachine

import libretto.StarterKit
import libretto.StarterKit._

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
        makeBeverage(espresso)(espressoOptions |*| ready)
      }
    }

  private def serveLatte: Done -⚬ (LatteOptions =⚬ Val[Beverage]) =
    λ { ready =>
      Λ { latteOptions =>
        makeBeverage(latte)(latteSpec(latteOptions) |*| ready)
      }
    }

  type LatteSpec = (Size, ShotCount, Option[Flavor])

  /**
   * The [[Done]] on the in-port signals readiness to make this beverage.
   * I.e., the output value will not be produced until the signal arrives
   */
  private def makeBeverage[Spec](
    f: Spec => Beverage,
  ): (Val[Spec] |*| Done) -⚬ Val[Beverage] =
    awaitPosSnd > mapVal(f)

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
