package libretto.examples.coffeemachine

import libretto.StarterKit
import libretto.StarterKit._

object CoffeeMachineProvider {
  import Protocol._

  val makeCoffeeMachine: Done -⚬ CoffeeMachine = rec { self =>
    val beverage: Done -⚬ (
      (EspressoMenu |*| CoffeeMachine) |&|
      (LatteMenu    |*| CoffeeMachine)
    ) =
      choice(
        onEspresso > snd(self),
        onLatte    > snd(self),
      )

    val end: Done -⚬ Done =
      id[Done]

    choice(beverage, end) > CoffeeMachine.pack
  }

  private def onEspresso: Done -⚬ (EspressoMenu |*| Done) =
    id                                       [                                           Done  ]
      .>(introFst(promise[ShotCount]))    .to[ (Neg[ShotCount]  |*|  Val[ShotCount]) |*| Done  ]
      .>(assocLR)                         .to[  Neg[ShotCount]  |*| (Val[ShotCount]  |*| Done) ]
      .>.snd(makeBeverage(espresso))      .to[  Neg[ShotCount]  |*| (Val[Beverage]   |*| Done) ]
                                          .to[  ShotCountChoice |*| (Val[Beverage]   |*| Done) ]
      .>(assocRL)                         .to[ (ShotCountChoice |*|  Val[Beverage])  |*| Done  ]
                                          .to[             EspressoMenu              |*| Done  ]

  private def onLatte: Done -⚬ (LatteMenu |*| Done) =
    id                                       [                                              Done  ]
      .>(introFst(promise[LatteParams]))  .to[ (Neg[LatteParams] |*|  Val[LatteParams]) |*| Done  ]
      .>(assocLR)                         .to[  Neg[LatteParams] |*| (Val[LatteParams]  |*| Done) ]
      .>.fst(collectLatteParams)          .to[    LatteOptions   |*| (Val[LatteParams]  |*| Done) ]
      .>.snd(makeBeverage(latte))         .to[    LatteOptions   |*| (Val[Beverage]     |*| Done) ]
      .>(assocRL)                         .to[   (LatteOptions   |*|  Val[Beverage])    |*| Done  ]
                                          .to[                LatteMenu                 |*| Done  ]

  private object CoffeeMachine {
    // Hides one level of recursive definition of CoffeeMachine.
    // It is just `pack` from the DSL applied to a type argument, in order to help type inference.
    def pack: (
      (EspressoMenu |*| CoffeeMachine) |&|
      (LatteMenu    |*| CoffeeMachine) |&|
      Done
    ) -⚬ CoffeeMachine =
      StarterKit.pack[[X] =>> (EspressoMenu |*| X) |&| (LatteMenu |*| X) |&| Done]
  }

  /**
   * ```
   * ┏━━━━━━━━━━━━━━━━┯━━━━━━━━━━━━━━━┯━━━━━━━━━━━━━━━━━━━━━━━┓
   * ┞─────────┐      ╎               ╎                       ┞─────────────┐
   * ╎Val[Spec]│→┄┄┐  ╎               ╎                   ┌┄┄→╎Val[Beverage]│
   * ┟─────────┘   ┆  ├─────────┐     ├─────────────┐     ┆   ┟─────────────┘
   * ┃             ├┄→╎Val[Spec]│→┄┄┄→╎Val[Beverage]│→┄┄┄→┤   ┨
   * ┞─────────┐   ┆  ├─────────┘     ├─────────────┘     ┆   ┞─────────────┐
   * ╎  Done   │→┄┄┘  ╎               ╎                   └┄┄→╎    Done     │
   * ┟─────────┘      ╎               ╎                       ┟─────────────┘
   * ┗━━━━━━━━━━━━━━━━┷━━━━━━━━━━━━━━━┷━━━━━━━━━━━━━━━━━━━━━━━┛
   *
   * ```
   *
   * The [[Done]] on the in-port signals readiness to make this beverage.
   * The [[Done]] on the out-port signals this beverage has been made.
   */
  private def makeBeverage[Spec](
    f: Spec => Beverage,
  ): (Val[Spec] |*| Done) -⚬ (Val[Beverage] |*| Done) =
    awaitPosSnd > mapVal(f) > signalPosSnd

  private def collectLatteParams: Neg[LatteParams] -⚬ LatteOptions =
    id                                                           [                       LatteOptions                      ]
                                                            .from[ (Neg[Size] |*| Neg[ShotCount]) |*| Neg[Option[Flavor]]  ]
      .<.fst(liftNegPair)                                   .from[ Neg[ (Size   ,     ShotCount)] |*| Neg[Option[Flavor]]  ]
      .<(liftNegPair)                                       .from[ Neg[((Size   ,     ShotCount)   ,      Option[Flavor])] ]
      .<(contramapNeg { case ((a, b), c) => (a, b, c) })    .from[ Neg[( Size   ,     ShotCount    ,      Option[Flavor])] ]
                                                            .from[ Neg[              LatteParams                         ] ]

  private def espresso(shots: ShotCount): Beverage =
    Beverage("Espresso" + (shots match {
      case ShotCount.Double => " doppio"
      case ShotCount.Single => ""
    }))

  private def latte(params: LatteParams): Beverage = {
    val (size, shots, flavor) = params
    val flavorStr = flavor.map(_.toString.toLowerCase + " ").getOrElse("")
    val shotsStr = shots match {
      case ShotCount.Double => " with an extra shot"
      case ShotCount.Single => ""
    }
    Beverage(s"$size ${flavorStr}latte$shotsStr")
  }
}
