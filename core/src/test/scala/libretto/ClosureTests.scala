package libretto

class ClosureTests extends TestSuite {
  import kit.dsl._
  import kit.dsl.$._

  test("simplest closure") {
    val f: Done -⚬ (Done =⚬ (Done |*| Done)) =
      λ { d1 =>
        Λ { d2 =>
          d1 |*| d2
        }
      }
  }

  test("some closure 0") {
    val f: (Done |*| Done) -⚬ (Done |*| Done) =
      λ { d =>
        val (d1 |*| d2) = d
        val f: $[Done =⚬ (Done |*| Done)] =
          Λ { d3 =>
            d3 |*| d2
          }
        f(d1)
      }
  }

  test("some closure 1") {
    val f: Done -⚬ (Done |*| Done) =
      λ { d =>
        val (d1 |*| d2) = d > fork
        val f: $[Done =⚬ (Done |*| Done)] =
          Λ { d3 =>
            d3 |*| d2
          }
        f(d1)
      }
  }

  test("some closure 2") {
    val f: Done -⚬ (Val[String] =⚬ Val[String]) =
      λ { (d: $[Done]) =>
        val n: $[Val[Int]] = d > constVal(2)
        val f: $[Val[String] =⚬ Val[String]] =
          Λ { s =>
            (n |*| s) > unliftPair > mapVal { case (n, s) => s.repeat(n) }
          }
        f
      }

    val prg: Done -⚬ Val[String] =
      forkMap(f, constVal("abc")) > eval

    assertVal(prg, "abcabc")
  }

  test("some closure 3") {
    val prg = λ { (d: $[Done]) =>
      val (d1 |*| d2) = d > fork
      val n: $[Val[Int]] = d1 > constVal(2)
      val f: $[Val[String] =⚬ Val[String]] =
        Λ { s =>
          (n |*| s) > unliftPair > mapVal { case (n, s) => s.repeat(n) }
        }
      val s = d2 > constVal("abc")
      f(s)
    }

    assertVal(prg, "abcabc")
  }
}
