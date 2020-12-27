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
    assertResult(done >>> constVal(5), 5)
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

    assertResult(raceKeepWinner(a, b), 'A')
  }
  
  test("delayed chooseL") {
    // 'A' delayed by 40 millis
    val a: One -⚬ Val[Char] =
      done >>> delay(40.millis) >>> constVal('A')
    
    // 'B' delayed by 30 + 20 = 50 millis.
    // We are testing that the second timer starts ticking only after the delayed choice is made.
    val b: One -⚬ Val[Char] =
      done >>> fork(delay(30.millis), choice(delay(20.millis), id)) >>> joinChooseL >>> constVal('B')

    assertResult(raceKeepWinner(a, b), 'A')    
  }
}
