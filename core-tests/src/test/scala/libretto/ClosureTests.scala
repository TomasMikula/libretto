package libretto

import libretto.testing.scalatest.TestSuite

class ClosureTests extends TestSuite {
  import kit.dsl._
  import kit.dsl.$._
  import kit.coreLib._

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

  test("`one` expression in a closure") {
    val p1: Done -⚬ (-[Val[Int]] |*| Val[Int]) =
      λ { d =>
        Λ { (i: $[Val[Int]]) =>
          val j = one > done > constVal(1)
          val res = (i * j) > mapVal(_ + _)
          (res |*| d) > awaitPosSnd
        }
      }

    val p2: Done -⚬ Val[Int] =
      p1 > λ { case (out |*| in) =>
        val x = one > done > constVal(42)
        in alsoElim supply(x |*| out)
      }

    assertVal(p2, 43)
  }
}
