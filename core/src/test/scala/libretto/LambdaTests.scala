package libretto

class LambdaTests extends TestSuite {
  import kit.dsl._
  import kit.coreLib._
  import kit.scalaLib._

  test("λ-expression compilation") {
    import $._

    def f = λ { (t: $[Ping |*| (Done |*| Val[String])]) =>
      val (p |*| (d |*| s)) = t
      val i = (s |*| p) > awaitPingSnd > mapVal(_.length)
      d |*| i
    }
  }
}
