package libretto

import libretto.puro.PuroLib
import libretto.scaletto.ScalettoLib
import libretto.testing.TestCase
import libretto.testing.scaletto.ScalettoTestKit
import libretto.testing.scalatest.scaletto.ScalatestScalettoTestSuite

class ClosureTests extends ScalatestScalettoTestSuite {
  override def testCases(using kit: ScalettoTestKit): List[(String, TestCase[kit.type])] = {
    import kit.dsl.*
    import kit.Outcome
    import kit.Outcome.{assertEquals, assertNotThrows}

    val puroLib = PuroLib(kit.dsl)
    val scalettoLib = ScalettoLib(kit.dsl, puroLib)
    import puroLib.*
    import scalettoLib.{*, given}

    List(
      "simplest closure" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            val f: Done -⚬ (Done =⚬ (Done |*| Done)) =
              λ { d1 =>
                λ.closure { d2 =>
                  d1 |*| d2
                }
              }
            f
          }
        },

      "some closure 0" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            val f: (Done |*| Done) -⚬ (Done |*| Done) =
              λ { d =>
                val (d1 |*| d2) = d
                val f: $[Done =⚬ (Done |*| Done)] =
                  λ.closure { d3 =>
                    d3 |*| d2
                  }
                f(d1)
              }
            f
          }
        },

      "some closure 1" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            val f: Done -⚬ (Done |*| Done) =
              λ { d =>
                val (d1 |*| d2) = d |> fork
                val f: $[Done =⚬ (Done |*| Done)] =
                  λ.closure { d3 =>
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
              val n: $[Val[Int]] = d |> constVal(2)
              val f: $[Val[String] =⚬ Val[String]] =
                λ.closure { s =>
                  (n |*| s) |> unliftPair |> mapVal { case (n, s) => s.repeat(n) }
                }
              f
            }

          val prg: Done -⚬ Val[String] =
            forkMap(f, constVal("abc")) > eval

          prg
        }.via {
          _.expectVal.flatMap(assertEquals(_, "abcabc"))
        },

      "some closure 3" ->
        TestCase.interactWith {
          λ { (d: $[Done]) =>
            val (d1 |*| d2) = d |> fork
            val n: $[Val[Int]] = d1 |> constVal(2)
            val f: $[Val[String] =⚬ Val[String]] =
              λ.closure { s =>
                (n |*| s) |> unliftPair |> mapVal { case (n, s) => s.repeat(n) }
              }
            val s = d2 |> constVal("abc")
            f(s)
          }
        }.via {
          _.expectVal.flatMap(assertEquals(_, "abcabc"))
        },

      "`one` expression in a closure" ->
        TestCase.interactWith {
          val p1: Done -⚬ (-[Val[Int]] |*| Val[Int]) =
            λ { d =>
              λ.closure { (i: $[Val[Int]]) =>
                val j = $.one |> done |> constVal(1)
                val res = (i ** j) |> mapVal(_ + _)
                (res |*| d) |> awaitPosSnd
              }
            }

          val p2: Done -⚬ Val[Int] =
            p1 > λ { case (out |*| in) =>
              val x = $.one |> done |> constVal(42)
              in alsoElim supply(x |*| out)
            }

          p2
        }.via {
          _.expectVal.flatMap(assertEquals(_, 43))
        },

      "non-capturing 'closure' (higher-order function)" ->
        TestCase.awaitDone {
          val f: Done -⚬ (Done |*| (Done =⚬ Done)) =
            λ { x =>
              x |*| (
                λ.closure { y => y } // does not capture anything from the outer scope
              )
            }
          val g: (Done |*| (Done =⚬ Done)) -⚬ Done =
            λ { case d |*| f =>
              f(d)
            }
          λ { d => g(f(d)) }
        },

      "closure capturing semigroupal variable" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ.from[Done] { case +(a) =>
              λ.closure { (b: $[Done]) =>
                a |*| b |*| a
              }
            }
          }
        },

      "closure with semigroupal variable" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ { (a: $[Done]) =>
              λ.closure.from[Done] { case +(b) =>
                b |*| a |*| b
              }
            }
          }
        },

      "nested closures with semigroupal variables" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ.from[Done] { case +(a) =>
              λ.closure.from[Done] { case +(b) =>
                λ.closure.from[Done] { case +(c) =>
                  λ.closure.from[Done] { case +(d) =>
                    ((c |*| d) |*| (b |*| a)) |*| ((d |*| (a |*| a)) |*| (c |*| b))
                  } |*|
                  λ.closure.from[Done] { case +(d) =>
                    ((c |*| d) |*| (b |*| a)) |*| ((d |*| (a |*| a)) |*| (c |*| b))
                  }
                } |*|
                λ.closure.from[Done] { case +(d) =>
                  (d |*| (b |*| a)) |*| ((d |*| (a |*| a)) |*| b)
                }
              } |*|
              λ.closure.from[Done] { case +(c) =>
                λ.closure.from[Done] { case +(d) =>
                  ((a |*| d) |*| a) |*| ((d |*| (c |*| a)) |*| (c |*| c))
                } |*|
                λ.closure.from[Done] { case +(d) =>
                  ((c |*| d) |*| (d |*| a)) |*| ((d |*| (a |*| a)) |*| c)
                }
              }
            }
          }
        },

      "capture one-expression" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ { (a: $[Done]) =>
              val b: $[Done] = $.one |> done
              λ.closure { (c: $[Done]) =>
                a |*| b |*| c
              }
            }
          }
        },

      "return only captured one-expression" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ.from[One] { case ?(_) =>
              val b: $[Done] = $.one |> done
              λ.closure.from[One] { case ?(_) =>
                b
              }
            }
          }
        },

      "capture one-expression into another one-expression" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ.from[One] { case ?(_) =>
              val b = $.one |> done
              λ.closure.from[One] { case ?(_) =>
                val c = $.one |> done
                b |*| c
              }
            }
          }
        },

      "capture two one-expressions into another one-expression" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ.from[One] { case ?(_) =>
              val b = $.one |> done
              val c = $.one |> done
              λ.closure.from[One] { case ?(_) =>
                b |*| c
              }
            }
          }
        },

      "fork a one-expression inside closure" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ { (a: $[Done]) =>
              λ.closure { (b: $[Done]) =>
                val (c |*| d) = $.one |> done |> fork
                a |*| b |*| c |*| d
              }
            }
          }
        },


      "one-expression whose part is consumed outside and part inside a closure" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ { (a: $[Done]) =>
              val (b |*| c) = $.one |> done |> fork
              λ.closure { (d: $[Done]) =>
                c |*| d
              } |*| (a |*| b)
            }
          }
        },

      "non-linearity in nested context does not affect parent context" ->
        TestCase.pure {
          for {
            e <- Outcome.assertThrows {
              λ { (a: $[Done]) =>
                λ.closure { (b: $[Done]) =>
                  a match {
                    case +(a) =>
                      a |*| b
                  }
                } |*| a
              }
            }
            _ <- Outcome.assertSubstring("used more than once", e.getMessage)
            _ <- Outcome.assertSubstring("variable bound by lambda", e.getMessage)
            _ <- Outcome.assertSubstring("ClosureTests.scala:269", e.getMessage)
          } yield ()
        },

      "semigroup evidence in nested scope" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ { (a: $[Done]) =>
              λ.closure { (b: $[Done]) =>
                a match {
                  case +(a) =>
                    a |*| b |*| a
                }
              }
            }
          }
        },

      "discard from a nested context" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ { (a: $[One]) =>
              λ.closure { (d: $[Done]) =>
                a match        // `a` was introduced in parent context
                  case ?(_) => // but is discarded in this (nested) context
                    d
              }
            }
          }
        },

      "discard both projections from a nested context" ->
        TestCase.pure {
          Outcome.assertNotThrows {
            λ { (a: $[One |*| One]) =>
              λ.closure { (d: $[Done]) =>
                a match                 // `a` was introduced in parent context
                  case ?(_) |*| ?(_) => // but is decomposed and discarded in this (nested) context
                    d
              }
            }
          }
        },
    )
  }
}
