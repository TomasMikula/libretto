package libretto

import libretto.scaletto.ScalettoLib
import libretto.testing.TestCase
import libretto.testing.scaletto.ScalettoTestKit
import libretto.testing.scalatest.scaletto.ScalatestScalettoTestSuite
import libretto.util.Monad.syntax._

class LambdaTests extends ScalatestScalettoTestSuite {
  override def testCases(using kit: ScalettoTestKit): List[(String, TestCase[kit.type])] = {
    import kit.dsl
    import kit.dsl._
    import kit.dsl.$._
    import kit.Outcome.{assertSubstring, expectNotThrows, expectThrows}
    import kit.expectVal

    val coreLib = CoreLib(dsl)
    val scalettoLib = ScalettoLib(dsl, coreLib)
    import coreLib._
    import scalettoLib._

    def c(c: Char): Done -⚬ Val[Char] =
      constVal(c)

    List(
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
            e <- expectThrows {
              λ { (trigger: $[Done]) =>
                val (d1 |*| d2) = fork(trigger)
                d1
              }
            }
            _ <- assertSubstring("not fully consumed", e.getMessage)
            _ <- assertSubstring("The second half of untupling", e.getMessage)
            _ <- assertSubstring("LambdaTests.scala:124", e.getMessage)
          } yield ()
        },

      "overused variable" ->
        TestCase.testOutcome {
          for {
            e <- expectThrows {
              λ { (trigger: $[Done]) =>
                join(trigger |*| trigger)
              }
            }
            _ <- assertSubstring("used more than once", e.getMessage)
            _ <- assertSubstring("The variable bound by lambda expression at", e.getMessage)
            _ <- assertSubstring("LambdaTests.scala:138", e.getMessage)
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
            e <- expectThrows {
              λ { d =>
                one > done
              }
            }
            _ <- assertSubstring("not fully consumed", e.getMessage)
            _ <- assertSubstring("The variable bound by lambda expression at", e.getMessage)
            _ <- assertSubstring("LambdaTests.scala:180", e.getMessage)
          } yield ()
        },

      "affine variable" ->
        TestCase.multiple(
          "unused" ->
            TestCase.testOutcome {
              expectNotThrows {
                val prg: One -⚬ Done =
                  λ.? { _ =>
                    one > done
                  }
                prg
              }
            },
          "used once" ->
            TestCase.testOutcome {
              expectNotThrows {
                val prg: One -⚬ One =
                  λ.? { d => d }
                prg
              }
            },
          "used twice" ->
            TestCase.testOutcome {
              for {
                e <- expectThrows {
                  λ.? { (x: $[One]) => x |*| x }
                }
                _ <- assertSubstring("used more than once", e.getMessage)
                _ <- assertSubstring("variable bound by lambda expression at", e.getMessage)
                _ <- assertSubstring("LambdaTests.scala:214", e.getMessage)
              } yield ()
            },
        ),

      "cosemigroupal variable" ->
        TestCase.multiple(
          "used once" ->
            TestCase.testOutcome {
              expectNotThrows {
                λ.+ { (d: $[Done]) => d }
              }
            },
          "used twice" ->
            TestCase.testOutcome {
              expectNotThrows {
                λ.+ { (d: $[Done]) => d |*| d }
              }
            },
          "unused" ->
            TestCase.testOutcome {
              for {
                e <- expectThrows {
                  λ.+ { (_: $[Done]) => one > done }
                }
                _ <- assertSubstring("not fully consumed", e.getMessage)
                _ <- assertSubstring("variable bound by lambda expression at", e.getMessage)
                _ <- assertSubstring("LambdaTests.scala:241", e.getMessage)
              } yield ()
            },
          "used twice, with a twist" ->
            TestCase.testOutcome {
              expectNotThrows {
                λ.+ { (d: $[Done]) =>
                  val (p |*| q) = fork(d)
                  val (r |*| s) = fork(d)
                  (p |*| r) |*| (q |*| s)
                }
              }
            },
          "derived expressions remain linear" ->
            TestCase.testOutcome {
              for {
                e <- expectThrows {
                  λ.+ { (d: $[Done]) =>
                    val someExpensiveOrSideEffectingFunction = id[Done]
                    val x = someExpensiveOrSideEffectingFunction(d)
                    x |*| x
                  }
                }
                _ <- assertSubstring("used more than once", e.getMessage)
                _ <- assertSubstring("LambdaTests.scala:264", e.getMessage)
              } yield ()
            }
        ),

      "comonoidal variable" ->
        TestCase.multiple(
          "used once" ->
            TestCase.testOutcome {
              expectNotThrows {
                λ.* { (p: $[Ping]) => p }
              }
            },
          "used twice" ->
            TestCase.testOutcome {
              expectNotThrows {
                λ.* { (p: $[Ping]) => p |*| p }
              }
            },
          "unused" ->
            TestCase.testOutcome {
              expectNotThrows {
                λ.* { (_: $[Ping]) => one > done }
              }
            },
        ),

      "non-linear variable via pattern match" ->
        TestCase.testOutcome {
          expectNotThrows {
            λ { (a: $[One]) =>
              a match
                case $.*(a) =>
                  (a, a) match
                    case (?(a0), a) =>
                      a |*| a
            }
          }
        }
    )
  }
}
