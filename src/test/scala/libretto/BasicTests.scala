package libretto

import scala.collection.mutable
import scala.concurrent.duration._

class BasicTests extends TestSuite {
  import kit.dsl._
  import kit.coreLib._
  import kit.scalaLib._

  private def raceKeepWinner[A](
    prg1: One -⚬ Val[A],
    prg2: One -⚬ Val[A],
  ): One -⚬ Val[A] =
    parFromOne(prg1, prg2)
      .race(
        caseFstWins = id.joinR(neglect),
        caseSndWins = id.joinL(neglect),
      )

  test("done") {
    assertCompletes(done)
  }

  test("join ⚬ fork") {
    assertCompletes(done >>> fork >>> join)
  }

  test("constVal") {
    assertVal(done >>> constVal(5), 5)
  }

  test("unliftEither") {
    assertVal(const(42) >>> injectR >>> unliftEither, Right(42))
  }

  test("liftPair, liftNegPair") {
    val prg: One -⚬ Val[(String, Int)] =
      id                                       [       One                                                                            ]
        .>(const(("foo", 42)))              .to[     Val[(String, Int)]                                                               ]
        .introSnd(promise)                  .to[     Val[(String, Int)]      |*| (   Neg[(String, Int)]       |*| Val[(String, Int)]) ]
        .assocRL                            .to[ (   Val[(String, Int)]      |*|     Neg[(String, Int)]     ) |*| Val[(String, Int)]  ]
        .>.fst(par(liftPair, liftNegPair))  .to[ ((Val[String] |*| Val[Int]) |*|  (Neg[String] |*| Neg[Int])) |*| Val[(String, Int)]  ]
        .>.fst(rInvert).elimFst             .to[                                                                  Val[(String, Int)]  ]

    assertVal(prg, ("foo", 42))
  }

  test("unliftPair, unliftNegPair") {
    val lInvert: One -⚬ ((Neg[String] |*| Neg[Int])  |*| (Val[String] |*| Val[Int])) =
      coreLib.lInvert

    val prg: One -⚬ Val[(String, Int)] =
      id                                           [               One                                                                            ]
        .>(parFromOne(const("foo"), const(42))) .to[   Val[String] |*| Val[Int]                                                                   ]
        .introSnd.>.snd(lInvert)                .to[  (Val[String] |*| Val[Int]) |*| ((Neg[String] |*| Neg[Int])  |*| (Val[String] |*| Val[Int])) ]
        .assocRL                                .to[ ((Val[String] |*| Val[Int]) |*|  (Neg[String] |*| Neg[Int])) |*| (Val[String] |*| Val[Int])  ]
        .>.fst(par(unliftPair, unliftNegPair))  .to[ (    Val[(String, Int)]     |*|      Neg[(String, Int)]    ) |*| (Val[String] |*| Val[Int])  ]
        .elimFst(fulfill)                       .to[                                                                   Val[String] |*| Val[Int]   ]
        .>(unliftPair)                          .to[                                                                      Val[(String, Int)]      ]

    assertVal(prg, ("foo", 42))
  }

  test("inflate") {
    val prg: One -⚬ Done =
      id                                 [    One                            ]
        .>(const(42))                 .to[  Val[Int]                         ]
        .>(introSnd(lInvertSignal))   .to[  Val[Int] |*| ( Need    |*| Done) ]
        .assocRL                      .to[ (Val[Int] |*|   Need  ) |*| Done  ]
        .>.fst.snd(inflate)           .to[ (Val[Int] |*| Neg[Int]) |*| Done  ]
        .elimFst(fulfill)             .to[                             Done  ]

    assertCompletes(prg)
  }

  test("delayed injectL") {
    // 'A' delayed by 40 millis
    val a: One -⚬ Val[Char] =
      done >>> delay(40.millis) >>> constVal('A')

    // 'B' delayed by 30 + 20 = 50 millis.
    // We are testing that the second timer starts ticking only after the delayed inject (joinInjectL).
    val b: One -⚬ Val[Char] = {
      val delayedInjectL: One -⚬ (Val[Char] |+| Val[Char]) =
        done >>> fork(delay(30.millis), constVal('B')) >>> joinInjectL
      delayedInjectL >>> either(
        introFst[Val[Char], Done](done >>> delay(20.millis)).joinL,
        id,
      )
    }

    assertVal(raceKeepWinner(a, b), 'A')
  }

  test("delayed chooseL") {
    // 'A' delayed by 40 millis
    val a: One -⚬ Val[Char] =
      done >>> delay(40.millis) >>> constVal('A')

    // 'B' delayed by 30 + 20 = 50 millis.
    // We are testing that the second timer starts ticking only after the delayed choice is made.
    val b: One -⚬ Val[Char] =
      done >>> fork(delay(30.millis), choice(delay(20.millis), id)) >>> joinChooseL >>> constVal('B')

    assertVal(raceKeepWinner(a, b), 'A')
  }

  test("crash") {
    assertCrashes(done >>> crashd("boom!"), "boom!")
  }

  test("crash - even if it loses a race, the program still crashes") {
    val prg = done
      .>>>( fork(id, delay(10.millis) >>> crashd("oops")) )
      .>>>( raceCompletion )
      .>>>( either(id, id) )
    assertCrashes(prg, "oops")
  }

  test("crash in non-executed |+| has no effect") {
    val prg = done
      .injectL[Done]
      .either(id, crashd("bang!"))
    assertCompletes(prg)
  }

  test("crash in non-chosen |&| alternative has no effect") {
    val prg = done
      .choice(id, crashd("bang!"))
      .chooseL
    assertCompletes(prg)
  }

  test("coDistribute") {
    type B = Val[Boolean]
    type C = Val[Char]
    type I = Val[Int]
    type S = Val[String]

    //               (false   1)    (true "foo")    ('a'    2)    ('b'  "bar")
    val init: One -⚬ (((B |*| I) |&| (B |*| S)) |&| ((C |*| I) |&| (C |*| S))) =
      choice(
        choice(
          parFromOne(const(false), const(1)),
          parFromOne(const(true), const("foo")),
        ),
        choice(
          parFromOne(const('a'), const(2)),
          parFromOne(const('b'), const("bar")),
        ),
      )

    val coDistributed1: One -⚬ ((B |&| C) |*| (I |&| S)) =
      init
        .bimap(coDistributeL, coDistributeL)
        .>(coDistributeR)

    val coDistributed2: One -⚬ ((B |&| C) |*| (I |&| S)) =
      init                                          .to[ ((B |*| I) |&| (B  |*|  S)) |&| ((C |*| I) |&| (C  |*| S)) ]
        .>(|&|.IXI)                                 .to[ ((B |*| I) |&| (C  |*|  I)) |&| ((B |*| S) |&| (C  |*| S)) ]
        .bimap(coDistributeR, coDistributeR)        .to[ ((B        |&|  C) |*|  I ) |&| ((B        |&|  C) |*| S ) ]
        .>(coDistributeL)                           .to[  (B        |&|  C) |*| (I   |&|                        S ) ]

    case class Combination[X, Y](
      choose1: (B |&| C) -⚬ Val[X],
      choose2: (I |&| S) -⚬ Val[Y],
      expectedX: X,
      expectedY: Y,
    ) {
      type T = X
      type U = Y

      def go: ((B |&| C) |*| (I |&| S)) -⚬ Val[(T, U)] =
        par(choose1, choose2) >>> unliftPair

      def expected: (T, U) =
        (expectedX, expectedY)
    }

    val combinations = Seq(
      Combination(chooseL, chooseL, false, 1),
      Combination(chooseL, chooseR, true, "foo"),
      Combination(chooseR, chooseL, 'a', 2),
      Combination(chooseR, chooseR, 'b', "bar"),
    )

    for {
      f <- Seq(coDistributed1, coDistributed2)
      c <- combinations
    } {
      assertVal(f >>> c.go, c.expected)
    }
  }

  test("acquire - effect - transform - release") {
    class MVar[A](var value: A) {
      def set(a: A): MVar[A] = {
        this.value = a
        this
      }
    }

    val acquireFuns = Seq[Val[Int] -⚬ Res[MVar[Int]]](
      mVal(new MVar(_)),
      acquire0(new MVar(_), release = _ => ???),
      acquireAsync0(i => Async.defer(new MVar(i)), release = _ => ???),
    )

    val incFuns = Seq[Res[MVar[Int]] -⚬ Res[MVar[Int]]](
      effect0(i => i.set(i.value + 1)),
      effectAsync0(i => Async.defer(i.set(i.value + 1))),
      introSnd(const(())) > effect     [MVar[Int], Unit, Unit]((i, _) =>             i.set(i.value + 1) ) > effectWrAsync((_, _) => Async.defer(())),
      introSnd(const(())) > effectAsync[MVar[Int], Unit, Unit]((i, _) => Async.defer(i.set(i.value + 1))) > effectWr     ((_, _) =>             () ),
    )

    val toStringTrans = Seq[Res[MVar[Int]] -⚬ Res[MVar[String]]](
      transformResource0(i => new MVar(Integer.toString(i.value)), release = _ => ???),
      transformResourceAsync0(i => Async.defer(new MVar(Integer.toString(i.value))), release = _ => ???),
    )

    val releaseFuns = Seq[Res[MVar[String]] -⚬ Val[String]](
      release0(_.value),
      releaseAsync0(s => Async.defer(s.value)),
    )

    val prgs: Seq[One -⚬ Val[String]] = {
      for {
        acquireMVar <- acquireFuns
        incMVar <- incFuns
        mvarToString <- toStringTrans
        releaseMVar <- releaseFuns
      } yield {
        const(0)
          .>(acquireMVar)
          .>(incMVar)
          .>(mvarToString)
          .>(releaseMVar)
      }
    }

    for (prg <- prgs) {
      assertVal(prg, "1")
    }
  }

  test("release via registered function") {
    val ref = new java.util.concurrent.atomic.AtomicReference[String]("init")

    val prg: One -⚬ Done =
      const(()) > acquire0(identity, release = _ => ref.set("released")) > release

    assertCompletes(prg)
    assert(ref.get() == "released")
  }
}
