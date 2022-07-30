package libretto

import libretto.StarterKit.dsl._
import libretto.StarterKit.dsl.$._
import libretto.StarterKit.coreLib._
import libretto.testing.scalatest.ScalatestStarterTestSuite
import libretto.testing.Tests.Cases
import libretto.testing.{StarterTestKit, TestCase}
import libretto.testing.TestCase.testOutcome
import libretto.util.Monad.syntax._

class LambdaTests extends ScalatestStarterTestSuite {
  private def c(c: Char): Done -⚬ Val[Char] =
    constVal(c)

  override def testCases(using kit: StarterTestKit): Cases[kit.type] = {
    import kit.Outcome.{assertSubstring, expectThrow}
    import kit.expectVal

    Cases(
      "some λ-expressions" ->
        TestCase.interactWith {
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

          prg
        }.via {
          expectVal(_).assertEquals(3)
        },

      "shuffle 8 inputs (#1)" ->
        TestCase.interactWith {
          val prg: Done -⚬ Val[((((Char, Char), (Char, ((Char, Char), Char))), Char), Char)] =
            (((c('a') /\ c('b')) /\ c('c')) /\ ((c('d') /\ ((c('e') /\ c('f')) /\ c('g'))) /\ c('h')))
              > λ { case (((a |*| b) |*| c) |*| ((d |*| ((e |*| f) |*| g)) |*| h)) =>
                  (((g * d) * (b * ((f * h) * e))) * c) * a
                }
          prg
        }.via {
          expectVal(_).assertEquals((((('g', 'd'), ('b', (('f', 'h'), 'e'))), 'c'), 'a'))
        },

      "shuffle 8 inputs (#2)" ->
        TestCase.interactWith {
          val prg: Done -⚬ Val[((Char, (Char, (Char, Char))), ((Char, Char), (Char, Char)))] =
            ((c('a') /\ c('b')) /\ (c('c') /\ c('d'))) /\ (c('e') /\ (c('f') /\ (c('g') /\ c('h'))))
              > λ { case (((a |*| b) |*| (c |*| d)) |*| (e |*| (f |*| (g |*| h)))) =>
                  (h * (d * (b * f))) * ((c * g) * (a * e))
                }
          prg
        }.via {
          expectVal(_).assertEquals((('h', ('d', ('b', 'f'))), (('c', 'g'), ('a', 'e'))))
        },

      "shuffle 8 inputs (#3)" ->
        TestCase.interactWith {
          val prg: Done -⚬ Val[(Char, (Char, (Char, (Char, (Char, (Char, (Char, Char)))))))] =
            (c('a') /\ (c('b') /\ (c('c') /\ (c('d') /\ (c('e') /\ (c('f') /\ (c('g') /\ c('h'))))))))
              > λ { case (a |*| (b |*| (c |*| (d |*| (e |*| (f |*| (g |*| h))))))) =>
                  h * (g * (f * (e * (d * (c * (b * a))))))
                }
          prg
        }.via {
          expectVal(_).assertEquals(('h', ('g', ('f', ('e', ('d', ('c', ('b', 'a'))))))))
        },

      "shuffle 8 inputs (#4)" ->
        TestCase.interactWith {
          val prg: Done -⚬ Val[((Char, (Char, (Char, Char))), ((Char, Char), (Char, Char)))] =
            ((c('a') /\ c('b')) /\ ((((c('c') /\ (c('d') /\ c('e'))) /\ c('f')) /\ c('g')) /\ c('h')))
              > λ { case ((a |*| b) |*| ((((c |*| (d |*| e)) |*| f) |*| g) |*| h)) =>
                  (g * (c * (b * h))) * ((a * e) * (f * d))
                }
          prg
        }.via {
          expectVal(_).assertEquals((('g', ('c', ('b', 'h'))), (('a', 'e'), ('f', 'd'))))
        },

      "shuffle 8 inputs (#5)" ->
        TestCase.interactWith {
          val prg: Done -⚬ Val[((Char, Char), ((((Char, Char), Char), (Char, Char)), Char))] =
            ((c('a') /\ ((c('b') /\ ((c('c') /\ c('d')) /\ c('e'))) /\ c('f'))) /\ (c('g') /\ c('h')))
              > λ { case ((a |*| ((b |*| ((c |*| d) |*| e)) |*| f)) |*| (g |*| h)) =>
                  (h * c) * ((((f * b) * d) * (g * a)) * e)
                }
          prg
        }.via {
          expectVal(_).assertEquals((('h', 'c'), (((('f', 'b'), 'd'), ('g', 'a')), 'e')))
        },

      "shuffle 8 inputs (#6)" ->
        TestCase.interactWith {
          val prg: Done -⚬ Val[((((Char, Char), Char), Char), (((Char, Char), Char), Char))] =
            ((c('a') /\ (c('b') /\ c('c'))) /\ ((c('d') /\ (c('e') /\ c('f'))) /\ (c('g') /\ c('h'))))
              > λ { case ((a |*| (b |*| c)) |*| ((d |*| (e |*| f)) |*| (g |*| h))) =>
                  (((h * f) * c) * d) * (((a * g) * b) * e)
                }
          prg
        }.via {
          expectVal(_).assertEquals((((('h', 'f'), 'c'), 'd'), ((('a', 'g'), 'b'), 'e')))
        },

      "unused variable" ->
        TestCase.testOutcome {
          for {
            e <- expectThrow {
              λ { (trigger: $[Done]) =>
                val (d1 |*| d2) = fork(trigger)
                d1
              }
            }
            _ <- assertSubstring("not fully consumed", e.getMessage)
            _ <- assertSubstring("The second half of untupling", e.getMessage)
            _ <- assertSubstring("LambdaTests.scala:119", e.getMessage)
          } yield ()
        },

      "overused variable" ->
        TestCase.testOutcome {
          for {
            e <- expectThrow {
              λ { (trigger: $[Done]) =>
                join(trigger |*| trigger)
              }
            }
            _ <- assertSubstring("used more than once", e.getMessage)
            _ <- assertSubstring("The input of lambda expression ending at", e.getMessage)
            _ <- assertSubstring("LambdaTests.scala:135", e.getMessage)
          } yield ()
        },

      "`one` expression" ->
        TestCase.interactWith {
          val prg: Done -⚬ Val[(Int, String)] =
            λ { d =>
              (d > constVal(1)) * (one > done > constVal("x"))
            }
          prg
        }.via {
          expectVal(_).assertEquals((1, "x"))
        },

      "multiple `one` expressions" ->
        TestCase.interactWith {
          val prg: Done -⚬ Val[((String, String), String)] =
            λ { d =>
              val x = one > done > constVal("x")
              val y = one > done > constVal("y")
              val z = one > done > constVal("z")

              val xyz = (x * y) * z

              (xyz |*| d) > awaitPosSnd
            }
          prg
        }.via {
          expectVal(_).assertEquals((("x", "y"), "z"))
        },

      "unused variable, `one`-based result" ->
        TestCase.testOutcome {
          for {
            e <- expectThrow {
              λ { d =>
                one > done
              }
            }
            _ <- assertSubstring("not fully consumed", e.getMessage)
            _ <- assertSubstring("The input of lambda expression ending at", e.getMessage)
            _ <- assertSubstring("LambdaTests.scala:177", e.getMessage)
          } yield ()
        },
    )
  }
}
