package libretto

class BasicTests extends TestSuite {
  import kit.dsl._
  import kit.coreLib._

  test("done") {
    assertCompletes(done)
  }

  test("join ⚬ fork") {
    assertCompletes(done >>> fork >>> join)
  }

  test("constVal") {
    assertResult(done >>> constVal(5), 5)
  }
}
