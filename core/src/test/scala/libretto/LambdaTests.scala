package libretto

class LambdaTests extends TestSuite {
  import kit.dsl._
  import kit.coreLib._
  import kit.scalaLib._

  test("some λ-expressions") {
    import kit.dsl.$._

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
    import kit.dsl.$._

    val prg: Done -⚬ Val[((((Char, Char), (Char, ((Char, Char), Char))), Char), Char)] =
      (((c('a') /\ c('b')) /\ c('c')) /\ ((c('d') /\ ((c('e') /\ c('f')) /\ c('g'))) /\ c('h')))
        > λ { case (((a |*| b) |*| c) |*| ((d |*| ((e |*| f) |*| g)) |*| h)) =>
            (((g * d) * (b * ((f * h) * e))) * c) * a
          }

    assertVal(prg, (((('g', 'd'), ('b', (('f', 'h'), 'e'))), 'c'), 'a'))
  }

  test("shuffle 8 inputs (#2)") {
    import kit.dsl.$._

    val prg: Done -⚬ Val[((Char, (Char, (Char, Char))), ((Char, Char), (Char, Char)))] =
      ((c('a') /\ c('b')) /\ (c('c') /\ c('d'))) /\ (c('e') /\ (c('f') /\ (c('g') /\ c('h'))))
        > λ { case (((a |*| b) |*| (c |*| d)) |*| (e |*| (f |*| (g |*| h)))) =>
            (h * (d * (b * f))) * ((c * g) * (a * e))
          }

    assertVal(prg, (('h', ('d', ('b', 'f'))), (('c', 'g'), ('a', 'e'))))
  }

  test("shuffle 8 inputs (#3)") {
    import kit.dsl.$._

    val prg: Done -⚬ Val[(Char, (Char, (Char, (Char, (Char, (Char, (Char, Char)))))))] =
      (c('a') /\ (c('b') /\ (c('c') /\ (c('d') /\ (c('e') /\ (c('f') /\ (c('g') /\ c('h'))))))))
        > λ { case (a |*| (b |*| (c |*| (d |*| (e |*| (f |*| (g |*| h))))))) =>
            h * (g * (f * (e * (d * (c * (b * a))))))
          }

    assertVal(prg, ('h', ('g', ('f', ('e', ('d', ('c', ('b', 'a'))))))))
  }

  test("shuffle 8 inputs (#4)") {
    import kit.dsl.$._

    val prg: Done -⚬ Val[((Char, (Char, (Char, Char))), ((Char, Char), (Char, Char)))] =
      ((c('a') /\ c('b')) /\ ((((c('c') /\ (c('d') /\ c('e'))) /\ c('f')) /\ c('g')) /\ c('h')))
        > λ { case ((a |*| b) |*| ((((c |*| (d |*| e)) |*| f) |*| g) |*| h)) =>
            (g * (c * (b * h))) * ((a * e) * (f * d))
          }

    assertVal(prg, (('g', ('c', ('b', 'h'))), (('a', 'e'), ('f', 'd'))))
  }

  test("shuffle 8 inputs (#5)") {
    import kit.dsl.$._

    val prg: Done -⚬ Val[((Char, Char), ((((Char, Char), Char), (Char, Char)), Char))] =
      ((c('a') /\ ((c('b') /\ ((c('c') /\ c('d')) /\ c('e'))) /\ c('f'))) /\ (c('g') /\ c('h')))
        > λ { case ((a |*| ((b |*| ((c |*| d) |*| e)) |*| f)) |*| (g |*| h)) =>
            (h * c) * ((((f * b) * d) * (g * a)) * e)
          }

    assertVal(prg, (('h', 'c'), (((('f', 'b'), 'd'), ('g', 'a')), 'e')))
  }

  test("shuffle 8 inputs (#6)") {
    import kit.dsl.$._

    val prg: Done -⚬ Val[((((Char, Char), Char), Char), (((Char, Char), Char), Char))] =
      ((c('a') /\ (c('b') /\ c('c'))) /\ ((c('d') /\ (c('e') /\ c('f'))) /\ (c('g') /\ c('h'))))
        > λ { case ((a |*| (b |*| c)) |*| ((d |*| (e |*| f)) |*| (g |*| h))) =>
            (((h * f) * c) * d) * (((a * g) * b) * e)
          }

    assertVal(prg, (((('h', 'f'), 'c'), 'd'), ((('a', 'g'), 'b'), 'e')))
  }
}
