package libretto.examples.coffeemachine

import libretto.StarterKit._
import scala.concurrent.duration._

/**
 * A front panel of a coffee machine. Displays the menu and prompts the user for choices.
 */
object CoffeeMachineClient {
  import Protocol._

  val useCoffeeMachine: CoffeeMachine -⚬ Done = {
    def go: (Done |*| CoffeeMachine) -⚬ Done = rec { go =>
      snd(unpack) > mainMenu(go)
    }

    introFst(done) > go
  }

  private def mainMenu(
    repeat: (Done |*| CoffeeMachine) -⚬ Done,
  ): (Done |*| (((EspressoMenu |*| CoffeeMachine) |&| (LatteMenu |*| CoffeeMachine)) |&| Done)) -⚬ Done = {

    enum Item { case Espresso, Latte, Quit }
    object Item {
      // ¯\_(ツ)_/¯ Why doesn't the compiler know that Item =:= (Espresso.type | Latte.type | Quit.type)?
      def asUnion(i: Item): (Espresso.type | Latte.type | Quit.type) =
        i match {
          case Espresso => Espresso
          case Latte => Latte
          case Quit => Quit
        }
    }
    import Item._

    val msg =
      """Choose your beverage:
        | e - espresso
        | l - latte
        | q - quit
        |""".stripMargin

    val parse: String => Option[Item] = {
      case "e" => Some(Item.Espresso)
      case "l" => Some(Item.Latte)
      case "q" => Some(Item.Quit)
      case _   => None
    }

    val goEspresso: (Val[Espresso.type] |*| (EspressoMenu |*| CoffeeMachine)) -⚬ Done = fst(neglect) > VI(getEspresso) > repeat
    val goLatte:    (Val[Latte.type   ] |*| (LatteMenu    |*| CoffeeMachine)) -⚬ Done = fst(neglect) > VI(getLatte   ) > repeat
    val quit:       (Val[Quit.type    ] |*|              Done               ) -⚬ Done = fst(neglect) > join

    import ValMatcher.caseEq
    val chooseItem: (Val[Item] |*| (((EspressoMenu |*| CoffeeMachine) |&| (LatteMenu |*| CoffeeMachine)) |&| Done)) -⚬ Done =
      ( caseEq(Espresso) { goEspresso }
      & caseEq(Latte)    { goLatte    }
      & caseEq(Quit)     { quit       }
      )
        .contramapVal(Item.asUnion)
        .get

    id                               [   Done    |*| (((EspressoMenu |*| CoffeeMachine) |&| (LatteMenu |*| CoffeeMachine)) |&| Done) ]
      .>.fst(prompt(msg, parse))  .to[ Val[Item] |*| (((EspressoMenu |*| CoffeeMachine) |&| (LatteMenu |*| CoffeeMachine)) |&| Done) ]
      .>(chooseItem)              .to[           Done                                                                                ]
  }

  private def getEspresso: (Done |*| EspressoMenu) -⚬ Done =
    id                                 [  Done |*|             EspressoMenu            ]
                                    .to[  Done |*| (ShotCountChoice |*| Val[Beverage]) ]
      .>(assocRL)                   .to[ (Done |*| ShotCountChoice) |*| Val[Beverage]  ]
      .>.fst(promptShot)            .to[       Done                 |*| Val[Beverage]  ]
      .>(join(id, serve))           .to[                           Done                ]

  private def getLatte: (Done |*| LatteMenu) -⚬ Done =
    id                               [ Done |*|                                               LatteMenu                 ]
                                  .to[ Done |*| (((SizeChoice |*| ShotCountChoice) |*| FlavorChoice) |*| Val[Beverage]) ]
      .>.snd(assocLR > assocLR)   .to[ Done |*| (SizeChoice |*| (ShotCountChoice |*| (FlavorChoice |*| Val[Beverage]))) ]
      .>(VI(promptSize))          .to[      Done            |*| (ShotCountChoice |*| (FlavorChoice |*| Val[Beverage]))  ]
      .>(VI(promptShot))          .to[                      Done                 |*| (FlavorChoice |*| Val[Beverage])   ]
      .>(VI(promptFlavor))        .to[                                           Done              |*| Val[Beverage]    ]
      .>(join(id, serve))         .to[                                                            Done                  ]

  private def promptShot: (Done |*| ShotCountChoice) -⚬ Done = {
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

  private def promptSize: (Done |*| SizeChoice) -⚬ Done = {
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

  private def promptFlavor: (Done |*| FlavorChoice) -⚬ Done = {
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

  private def prompt[A](msg: String, parse: String => Option[A]): Done -⚬ Val[A] =
    rec { tryAgain =>
      printLine(msg)
        > readLine
        > mapVal { s => parse(s).toRight(()) }
        > liftEither
        > either(neglect > tryAgain, id)
    }

  private def fulfillAndSignal[A]: (Val[A] |*| Neg[A]) -⚬ Done =
    ΛI(signalPosFst) > elimSnd(fulfill)

  private def serve: Val[Beverage] -⚬ Done = {
    val dot: Done -⚬ Done = putStr(".") > delay(500.millis)
    val etc: Done -⚬ Done = dot > dot > dot > printLine("")

    delayVal(etc)
      .>(mapVal((b: Beverage) => s"☕ Here goes your ${b.description}."))
      .>(printLine)
      .>(etc)
      .>(printLine(""))
  }
}
