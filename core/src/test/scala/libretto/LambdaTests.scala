package libretto

class LambdaTests extends TestSuite {
  import kit.dsl._
  import kit.coreLib._
  import kit.scalaLib._

  test("λ-expression compilation") {
    import $._

    val f = λ { (t: $[Ping |*| (Done |*| Val[String])]) =>
      val (p |*| (d |*| s)) = t
      val i = (s |*| p) > awaitPingSnd > mapVal(_.length)
      d |*| i
    }

    val prg: Done -⚬ Val[Int] =
      λ { (d: $[Done]) =>
        val (p |*| d1) = d > notifyPosFst
        val (d2 |*| d3) = d1 > fork
        val s = constVal("foo")(d2)
        f(p |*| (d3 |*| s)) > awaitPosFst
      }

    assertVal(prg, 3)
  }
}
