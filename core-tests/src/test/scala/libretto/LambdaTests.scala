package libretto

import libretto.testing.TestSuite

class LambdaTests extends TestSuite {
  import kit.dsl._
  import kit.dsl.$._
  import kit.coreLib._
  import kit.scalaLib._

  test("some λ-expressions") {
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

  private def c(c: Char): Done -⚬ Val[Char] =
    constVal(c)

  test("shuffle 8 inputs (#1)") {
    val prg: Done -⚬ Val[((((Char, Char), (Char, ((Char, Char), Char))), Char), Char)] =
      (((c('a') /\ c('b')) /\ c('c')) /\ ((c('d') /\ ((c('e') /\ c('f')) /\ c('g'))) /\ c('h')))
        > λ { case (((a |*| b) |*| c) |*| ((d |*| ((e |*| f) |*| g)) |*| h)) =>
            (((g * d) * (b * ((f * h) * e))) * c) * a
          }

    assertVal(prg, (((('g', 'd'), ('b', (('f', 'h'), 'e'))), 'c'), 'a'))
  }

  test("shuffle 8 inputs (#2)") {
    val prg: Done -⚬ Val[((Char, (Char, (Char, Char))), ((Char, Char), (Char, Char)))] =
      ((c('a') /\ c('b')) /\ (c('c') /\ c('d'))) /\ (c('e') /\ (c('f') /\ (c('g') /\ c('h'))))
        > λ { case (((a |*| b) |*| (c |*| d)) |*| (e |*| (f |*| (g |*| h)))) =>
            (h * (d * (b * f))) * ((c * g) * (a * e))
          }

    assertVal(prg, (('h', ('d', ('b', 'f'))), (('c', 'g'), ('a', 'e'))))
  }

  test("shuffle 8 inputs (#3)") {
    val prg: Done -⚬ Val[(Char, (Char, (Char, (Char, (Char, (Char, (Char, Char)))))))] =
      (c('a') /\ (c('b') /\ (c('c') /\ (c('d') /\ (c('e') /\ (c('f') /\ (c('g') /\ c('h'))))))))
        > λ { case (a |*| (b |*| (c |*| (d |*| (e |*| (f |*| (g |*| h))))))) =>
            h * (g * (f * (e * (d * (c * (b * a))))))
          }

    assertVal(prg, ('h', ('g', ('f', ('e', ('d', ('c', ('b', 'a'))))))))
  }

  test("shuffle 8 inputs (#4)") {
    val prg: Done -⚬ Val[((Char, (Char, (Char, Char))), ((Char, Char), (Char, Char)))] =
      ((c('a') /\ c('b')) /\ ((((c('c') /\ (c('d') /\ c('e'))) /\ c('f')) /\ c('g')) /\ c('h')))
        > λ { case ((a |*| b) |*| ((((c |*| (d |*| e)) |*| f) |*| g) |*| h)) =>
            (g * (c * (b * h))) * ((a * e) * (f * d))
          }

    assertVal(prg, (('g', ('c', ('b', 'h'))), (('a', 'e'), ('f', 'd'))))
  }

  test("shuffle 8 inputs (#5)") {
    val prg: Done -⚬ Val[((Char, Char), ((((Char, Char), Char), (Char, Char)), Char))] =
      ((c('a') /\ ((c('b') /\ ((c('c') /\ c('d')) /\ c('e'))) /\ c('f'))) /\ (c('g') /\ c('h')))
        > λ { case ((a |*| ((b |*| ((c |*| d) |*| e)) |*| f)) |*| (g |*| h)) =>
            (h * c) * ((((f * b) * d) * (g * a)) * e)
          }

    assertVal(prg, (('h', 'c'), (((('f', 'b'), 'd'), ('g', 'a')), 'e')))
  }

  test("shuffle 8 inputs (#6)") {
    val prg: Done -⚬ Val[((((Char, Char), Char), Char), (((Char, Char), Char), Char))] =
      ((c('a') /\ (c('b') /\ c('c'))) /\ ((c('d') /\ (c('e') /\ c('f'))) /\ (c('g') /\ c('h'))))
        > λ { case ((a |*| (b |*| c)) |*| ((d |*| (e |*| f)) |*| (g |*| h))) =>
            (((h * f) * c) * d) * (((a * g) * b) * e)
          }

    assertVal(prg, (((('h', 'f'), 'c'), 'd'), ((('a', 'g'), 'b'), 'e')))
  }

  test("unused variable") {
    val e =
      intercept[Throwable] {
        λ { (trigger: $[Done]) =>
          val (d1 |*| d2) = fork(trigger)
          d1
        }
      }

    assert(e.getMessage contains "not fully consumed")
    assert(e.getMessage contains "The second half of untupling")
    assert(e.getMessage contains "LambdaTests.scala:96")
  }

  test("overused variable") {
    val e =
      intercept[Throwable] {
        λ { (trigger: $[Done]) =>
          join(trigger |*| trigger)
        }
      }

    assert(e.getMessage contains "used more than once")
    assert(e.getMessage contains "The input of lambda expression ending at")
    assert(e.getMessage contains "LambdaTests.scala:111")
  }
}
