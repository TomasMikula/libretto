package libretto.examples

import libretto.scaletto.StarterApp
import scala.concurrent.duration._

object CoffeeMachine extends StarterApp { app =>

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

  override def blueprint: Done -⚬ Done =
    makeCoffeeMachine > useCoffeeMachine

  def espresso(shots: ShotCount): Beverage =
    Beverage("Espresso" + (shots match {
      case ShotCount.Double => " doppio"
      case ShotCount.Single => ""
    }))

  def latte(params: LatteParams): Beverage = {
    val (size, shots, flavor) = params
    val flavorStr = flavor.map(_.toString.toLowerCase + " ").getOrElse("")
    val shotsStr = shots match {
      case ShotCount.Double => " with an extra shot"
      case ShotCount.Single => ""
    }
    Beverage(s"$size ${flavorStr}latte$shotsStr")
  }

  object CoffeeMachine {
    // Hides one level of recursive definition of CoffeeMachine.
    // It is just `pack` from the DSL applied to a type argument, in order to help type inference.
    def pack: (
      (EspressoMenu |*| CoffeeMachine) |&|
      (LatteMenu    |*| CoffeeMachine) |&|
      Done
    ) -⚬ CoffeeMachine =
      app.pack[[X] =>> (EspressoMenu |*| X) |&| (LatteMenu |*| X) |&| Done]
  }

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

  def onEspresso: Done -⚬ (EspressoMenu |*| Done) =
    id                                       [                                           Done  ]
      .>(introFst(promise[ShotCount]))    .to[ (Neg[ShotCount]  |*|  Val[ShotCount]) |*| Done  ]
      .>(assocLR)                         .to[  Neg[ShotCount]  |*| (Val[ShotCount]  |*| Done) ]
      .>.snd(makeBeverage(espresso))      .to[  Neg[ShotCount]  |*| (Val[Beverage]   |*| Done) ]
                                          .to[  ShotCountChoice |*| (Val[Beverage]   |*| Done) ]
      .>(assocRL)                         .to[ (ShotCountChoice |*|  Val[Beverage])  |*| Done  ]
                                          .to[             EspressoMenu              |*| Done  ]

  def onLatte: Done -⚬ (LatteMenu |*| Done) =
    id                                       [                                                 Done  ]
      .>(introFst(promise[LatteParams]))  .to[ (Neg[LatteParams]    |*|  Val[LatteParams]) |*| Done  ]
      .>(assocLR)                         .to[  Neg[LatteParams]    |*| (Val[LatteParams]  |*| Done) ]
      .>.fst(collectLatteParams)          .to[    LatteOptions      |*| (Val[LatteParams]  |*| Done) ]
      .>.snd(makeBeverage(latte))         .to[    LatteOptions      |*| (Val[Beverage]     |*| Done) ]
      .>(assocRL)                         .to[   (LatteOptions      |*|  Val[Beverage])    |*| Done  ]
                                          .to[                   LatteMenu                 |*| Done  ]

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
  def makeBeverage[Spec](
    f: Spec => Beverage,
  ): (Val[Spec] |*| Done) -⚬ (Val[Beverage] |*| Done) =
    awaitPosSnd > mapVal(f) > signalPosSnd

  def collectLatteParams: Neg[LatteParams] -⚬ LatteOptions =
    id                                                           [                       LatteOptions                      ]
                                                            .from[ (Neg[Size] |*| Neg[ShotCount]) |*| Neg[Option[Flavor]]  ]
      .<.fst(liftNegPair)                                   .from[ Neg[ (Size   ,     ShotCount)] |*| Neg[Option[Flavor]]  ]
      .<(liftNegPair)                                       .from[ Neg[((Size   ,     ShotCount)   ,      Option[Flavor])] ]
      .<(contramapNeg { case ((a, b), c) => (a, b, c) })    .from[ Neg[( Size   ,     ShotCount    ,      Option[Flavor])] ]
                                                            .from[ Neg[              LatteParams                         ] ]

  val useCoffeeMachine: CoffeeMachine -⚬ Done = {
    def go: (Done |*| CoffeeMachine) -⚬ Done = rec { go =>
      snd(unpack) > mainMenu(go)
    }

    introFst(done) > go
  }

  def mainMenu(
    repeat: (Done |*| CoffeeMachine) -⚬ Done,
  ): (Done |*| (((EspressoMenu |*| CoffeeMachine) |&| (LatteMenu |*| CoffeeMachine)) |&| Done)) -⚬ Done = {

    case class Espresso()
    case class Latte()
    case class Quit()
    type Item = Espresso | Latte | Quit

    val msg =
      """Choose your beverage:
        | e - espresso
        | l - latte
        | q - quit
        |""".stripMargin

    val parse: String => Option[Item] = {
      case "e" => Some(Espresso())
      case "l" => Some(Latte())
      case "q" => Some(Quit())
      case _   => None
    }

    val goEspresso: (Val[Espresso] |*| (EspressoMenu |*| CoffeeMachine)) -⚬ Done = fst(neglect) > VI(getEspresso) > repeat
    val goLatte:    (Val[Latte   ] |*| (LatteMenu    |*| CoffeeMachine)) -⚬ Done = fst(neglect) > VI(getLatte   ) > repeat
    val quit:       (Val[Quit    ] |*|              Done               ) -⚬ Done = fst(neglect) > join

    λ { case start |*| menu =>
      switch(start :>> prompt(msg, parse))
        .Case[Espresso] { e => goEspresso(e |*| chooseL(chooseL(menu))) }
        .Case[Latte]    { l => goLatte   (l |*| chooseR(chooseL(menu))) }
        .Case[Quit]     { q => quit      (q |*| chooseR(menu))          }
        .endswitch
    }
  }

  def getEspresso: (Done |*| EspressoMenu) -⚬ Done =
    id                                 [  Done |*|             EspressoMenu            ]
                                    .to[  Done |*| (ShotCountChoice |*| Val[Beverage]) ]
      .>(assocRL)                   .to[ (Done |*| ShotCountChoice) |*| Val[Beverage]  ]
      .>.fst(promptShot)            .to[       Done                 |*| Val[Beverage]  ]
      .>(joinMap(id, serve))        .to[                           Done                ]

  def getLatte: (Done |*| LatteMenu) -⚬ Done =
    id                               [ Done |*|                                               LatteMenu                 ]
                                  .to[ Done |*| (((SizeChoice |*| ShotCountChoice) |*| FlavorChoice) |*| Val[Beverage]) ]
      .>.snd(assocLR > assocLR)   .to[ Done |*| (SizeChoice |*| (ShotCountChoice |*| (FlavorChoice |*| Val[Beverage]))) ]
      .>(VI(promptSize))          .to[      Done            |*| (ShotCountChoice |*| (FlavorChoice |*| Val[Beverage]))  ]
      .>(VI(promptShot))          .to[                      Done                 |*| (FlavorChoice |*| Val[Beverage])   ]
      .>(VI(promptFlavor))        .to[                                           Done              |*| Val[Beverage]    ]
      .>(joinMap(id, serve))      .to[                                                            Done                  ]

  def promptShot: (Done |*| ShotCountChoice) -⚬ Done = {
    val msg =
      """Choose strength:
        | s - single espresso shot
        | d - double espresso shot
        |""".stripMargin

    val parse: String => Option[ShotCount] = {
      case "s" => Some(ShotCount.Single)
      case "d" => Some(ShotCount.Double)
      case _   => None
    }

    id[Done |*| ShotCountChoice]    .to[    Done        |*| Neg[ShotCount] ]
      .>.fst(prompt(msg, parse))    .to[ Val[ShotCount] |*| Neg[ShotCount] ]
      .>(fulfillAndSignal)          .to[                Done               ]
  }

  def promptSize: (Done |*| SizeChoice) -⚬ Done = {
    val msg =
      """Choose your size:
        | s - small
        | m - medium
        | l - large
        |""".stripMargin

    val parse: String => Option[Size] = {
      case "s" => Some(Size.Small)
      case "m" => Some(Size.Medium)
      case "l" => Some(Size.Large)
      case _   => None
    }

    id[Done |*| SizeChoice]         .to[    Done   |*| Neg[Size] ]
      .>.fst(prompt(msg, parse))    .to[ Val[Size] |*| Neg[Size] ]
      .>(fulfillAndSignal)          .to[           Done          ]
  }

  def promptFlavor: (Done |*| FlavorChoice) -⚬ Done = {
    val msg =
      """Do you want to add extra flavor to your latte?
        | v - vanilla
        | c - cinnamon
        | n - no extra flavor
        |""".stripMargin

    val parse: String => Option[Option[Flavor]] = {
      case "v" => Some(Some(Flavor.Vanilla))
      case "c" => Some(Some(Flavor.Cinnamon))
      case "n" => Some(None)
      case _   => None
    }

    id[Done |*| FlavorChoice]       .to[    Done             |*| Neg[Option[Flavor]] ]
      .>.fst(prompt(msg, parse))    .to[ Val[Option[Flavor]] |*| Neg[Option[Flavor]] ]
      .>(fulfillAndSignal)          .to[                     Done                    ]
  }

  def prompt[A](msg: String, parse: String => Option[A]): Done -⚬ Val[A] =
    rec { tryAgain =>
      printLine(msg)
        > readLine
        > mapVal { s => parse(s).toRight(()) }
        > liftEither
        > either(neglect > tryAgain, id)
    }

  def fulfillAndSignal[A]: (Val[A] |*| Neg[A]) -⚬ Done =
    ΛI(signalPosFst) > elimSnd(fulfill)

  def serve: Val[Beverage] -⚬ Done = {
    val dot: Done -⚬ Done = putStr(".") > delay(500.millis)
    val etc: Done -⚬ Done = dot > dot > dot > printLine("")

    delayVal(etc)
      .>(mapVal((b: Beverage) => s"☕ Here goes your ${b.description}."))
      .>(printLine)
      .>(etc)
      .>(printLine(""))
  }
}
