package libretto

import libretto.StarterKit.dsl._
import libretto.StarterKit.dsl.$._
import libretto.StarterKit.coreLib._
import libretto.testing.{StarterTestKit, TestCase}
import libretto.testing.scalatest.ScalatestStarterTestSuite

class ClosureTests extends ScalatestStarterTestSuite {
  override def testCases(using kit: StarterTestKit): List[(String, TestCase[kit.type])] = {
    import kit.{Outcome, expectVal}
    import kit.Outcome.expectNotThrows

    List(
      "simplest closure" ->
        TestCase.testOutcome {
          Outcome.expectNotThrows {
            val f: Done -⚬ (Done =⚬ (Done |*| Done)) =
              λ { d1 =>
                Λ { d2 =>
                  d1 |*| d2
                }
              }
            f
          }
        },

      "some closure 0" ->
        TestCase.testOutcome {
          Outcome.expectNotThrows {
            val f: (Done |*| Done) -⚬ (Done |*| Done) =
              λ { d =>
                val (d1 |*| d2) = d
                val f: $[Done =⚬ (Done |*| Done)] =
                  Λ { d3 =>
                    d3 |*| d2
                  }
                f(d1)
              }
            f
          }
        },

      "some closure 1" ->
        TestCase.testOutcome {
          Outcome.expectNotThrows {
            val f: Done -⚬ (Done |*| Done) =
              λ { d =>
                val (d1 |*| d2) = d > fork
                val f: $[Done =⚬ (Done |*| Done)] =
                  Λ { d3 =>
                    d3 |*| d2
                  }
                f(d1)
              }
            f
          }
        },

      "some closure 2" ->
        TestCase.interactWith {
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

          prg
        }.via {
          expectVal(_).assertEquals("abcabc")
        },

      "some closure 3" ->
        TestCase.interactWith {
          λ { (d: $[Done]) =>
            val (d1 |*| d2) = d > fork
            val n: $[Val[Int]] = d1 > constVal(2)
            val f: $[Val[String] =⚬ Val[String]] =
              Λ { s =>
                (n |*| s) > unliftPair > mapVal { case (n, s) => s.repeat(n) }
              }
            val s = d2 > constVal("abc")
            f(s)
          }
        }.via {
          expectVal(_).assertEquals("abcabc")
        },

      "`one` expression in a closure" ->
        TestCase.interactWith {
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

          p2
        }.via {
          expectVal(_).assertEquals(43)
        },
    )
  }
}
