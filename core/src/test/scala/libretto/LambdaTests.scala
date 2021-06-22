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

  test("shuffle 8 inputs") {
    import $._

    type C = Val[Char]

    val f: (((C |*| C) |*| C) |*| ((C |*| ((C |*| C) |*| C)) |*| C)) -⚬ ((((C |*| C) |*| (C |*| ((C |*| C) |*| C))) |*| C) |*| C) =
      λ { case (((a |*| b) |*| c) |*| ((d |*| ((e |*| f) |*| g)) |*| h)) =>
        (((g |*| d) |*| (b |*| ((f |*| h) |*| e))) |*| c) |*| a
      }

    val prg: Done -⚬ Val[((((Char, Char), (Char, ((Char, Char), Char))), Char), Char)] =
      constVal(((('a', 'b'), 'c'), (('d', (('e', 'f'), 'g')), 'h')))
        > liftPair > par(
          liftPair > fst(liftPair),
          liftPair > fst(liftPair > snd(liftPair > fst(liftPair))),
        )
        > f
        > fst(
          fst(
            par(
              unliftPair,
              snd(fst(unliftPair) > unliftPair) > unliftPair,
            ) > unliftPair
          ) > unliftPair
        ) > unliftPair

    assertVal(prg, (((('g', 'd'), ('b', (('f', 'h'), 'e'))), 'c'), 'a'))
  }
}
