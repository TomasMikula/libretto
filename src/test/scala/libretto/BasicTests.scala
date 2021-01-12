package libretto

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
}
