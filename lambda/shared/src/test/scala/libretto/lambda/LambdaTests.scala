package libretto.lambda

import libretto.lambda.Fun.*
import org.scalatest.funsuite.AnyFunSuite

class LambdaTests extends AnyFunSuite {
  type ->[A, B] = Fun[A, B]

  private def c(c: Char): One -> Val[Char] =
    constVal(c)

  test("some λ-expressions") {
    val f = λ { (t: $[One ** (One ** Val[String])]) =>
      val (u1 ** (u2 ** s)) = t
      val i = (s ** u1) > elimSnd > mapVal(_.length)
      u2 ** i
    }

    val prg: One -> Val[Int] =
      λ { (unit: $[One]) =>
        val (p ** d1) = unit > introFst
        val (d2 ** d3) = d1 > dup
        val s = constVal("foo")(d2)
        f(p ** (d3 ** s)) > elimFst
      }

    assert(compileToScala(prg)(()) == 3)
  }

  test("shuffle 8 inputs (#1)") {
    val prg: One -> Val[((((Char, Char), (Char, ((Char, Char), Char))), Char), Char)] =
      (((c('a') /\ c('b')) /\ c('c')) /\ ((c('d') /\ ((c('e') /\ c('f')) /\ c('g'))) /\ c('h')))
        > λ { case (((a ** b) ** c) ** ((d ** ((e ** f) ** g)) ** h)) =>
            (((g * d) * (b * ((f * h) * e))) * c) * a
          }
    val f = compileToScala(prg)
    assert(f(()) == (((('g', 'd'), ('b', (('f', 'h'), 'e'))), 'c'), 'a'))
  }

  test("shuffle 8 inputs (#2)") {
    val prg: One -> Val[((Char, (Char, (Char, Char))), ((Char, Char), (Char, Char)))] =
      ((c('a') /\ c('b')) /\ (c('c') /\ c('d'))) /\ (c('e') /\ (c('f') /\ (c('g') /\ c('h'))))
        > λ { case (((a ** b) ** (c ** d)) ** (e ** (f ** (g ** h)))) =>
            (h * (d * (b * f))) * ((c * g) * (a * e))
          }
    val f = compileToScala(prg)
    assert(f(()) == (('h', ('d', ('b', 'f'))), (('c', 'g'), ('a', 'e'))))
  }

  test("shuffle 8 inputs (#3)") {
    val prg: One -> Val[(Char, (Char, (Char, (Char, (Char, (Char, (Char, Char)))))))] =
      (c('a') /\ (c('b') /\ (c('c') /\ (c('d') /\ (c('e') /\ (c('f') /\ (c('g') /\ c('h'))))))))
        > λ { case (a ** (b ** (c ** (d ** (e ** (f ** (g ** h))))))) =>
            h * (g * (f * (e * (d * (c * (b * a))))))
          }
    val f = compileToScala(prg)
    assert(f(()) == ('h', ('g', ('f', ('e', ('d', ('c', ('b', 'a'))))))))
  }

  test("shuffle 8 inputs (#4)") {
    val prg: One -> Val[((Char, (Char, (Char, Char))), ((Char, Char), (Char, Char)))] =
      ((c('a') /\ c('b')) /\ ((((c('c') /\ (c('d') /\ c('e'))) /\ c('f')) /\ c('g')) /\ c('h')))
        > λ { case ((a ** b) ** ((((c ** (d ** e)) ** f) ** g) ** h)) =>
            (g * (c * (b * h))) * ((a * e) * (f * d))
          }
    val f = compileToScala(prg)
    assert(f(()) == (('g', ('c', ('b', 'h'))), (('a', 'e'), ('f', 'd'))))
  }

  test("shuffle 8 inputs (#5)") {
    val prg: One -> Val[((Char, Char), ((((Char, Char), Char), (Char, Char)), Char))] =
      ((c('a') /\ ((c('b') /\ ((c('c') /\ c('d')) /\ c('e'))) /\ c('f'))) /\ (c('g') /\ c('h')))
        > λ { case ((a ** ((b ** ((c ** d) ** e)) ** f)) ** (g ** h)) =>
            (h * c) * ((((f * b) * d) * (g * a)) * e)
          }
    val f = compileToScala(prg)
    assert(f(()) == (('h', 'c'), (((('f', 'b'), 'd'), ('g', 'a')), 'e')))
  }

  test("shuffle 8 inputs (#6)") {
    val prg: One -> Val[((((Char, Char), Char), Char), (((Char, Char), Char), Char))] =
      ((c('a') /\ (c('b') /\ c('c'))) /\ ((c('d') /\ (c('e') /\ c('f'))) /\ (c('g') /\ c('h'))))
        > λ { case ((a ** (b ** c)) ** ((d ** (e ** f)) ** (g ** h))) =>
            (((h * f) * c) * d) * (((a * g) * b) * e)
          }
    val f = compileToScala(prg)
    assert(f(()) == (((('h', 'f'), 'c'), 'd'), ((('a', 'g'), 'b'), 'e')))
  }

  test("unused variable") {
    val e = intercept[Exception] {
      λ { (trigger: $[One]) =>
        val (d1 ** d2) = dup(trigger)
        d1
      }
    }
    assert(e.getMessage `contains` "Unused variable")
    assert(e.getMessage `contains` "The second half of untupling")
    assert(e.getMessage `contains` "LambdaTests.scala:93")
  }

  test("overused variable") {
    val e = intercept[Exception] {
      λ { (trigger: $[One]) =>
        elimFst(trigger ** trigger)
      }
    }
    assert(e.getMessage `contains` "used more than once")
    assert(e.getMessage `contains` "The variable bound by lambda expression at")
    assert(e.getMessage `contains` "LambdaTests.scala:104")
  }

  test("`one` expression") {
    val prg: One -> Val[(Int, String)] =
      λ { d =>
        (d > constVal(1)) * (one > constVal("x"))
      }
    val f = compileToScala(prg)
    assert(f(()) == (1, "x"))
  }

  test("multiple `one` expressions") {
    val prg: One -> Val[((String, String), String)] =
      λ { d =>
        val x = one > constVal("x")
        val y = one > constVal("y")
        val z = one > constVal("z")

        val xyz = (x * y) * z

        (xyz ** d) > elimSnd
      }
    val f = compileToScala(prg)
    assert(f(()) == (("x", "y"), "z"))
  }

  test("unused variable, `one`-based result") {
    val e = intercept[Exception] {
      λ { d =>
        one
      }
    }
    assert(e.getMessage `contains` "Unused variable")
    assert(e.getMessage `contains` "The variable bound by lambda expression at")
    assert(e.getMessage `contains` "LambdaTests.scala:139")
  }

  test("affine variable: unused") {
    val prg: One -> One =
      λ.? { _ =>
        one
      }
    succeed
  }

  test("affine variable: used once") {
    val prg: One -> One =
      λ.? { d => d }
    succeed
  }

  test("affine variable: used twice") {
    val e = intercept[Exception] {
      λ.? { (x: $[One]) => x ** x }
    }
    assert(e.getMessage `contains` "used more than once")
    assert(e.getMessage `contains` "variable bound by lambda expression at")
    assert(e.getMessage `contains` "LambdaTests.scala:164")
  }

  test("cosemigroupal variable: used once") {
    λ.+ { (d: $[One]) => d }
    succeed
  }

  test("cosemigroupal variable: used twice") {
    λ.+ { (d: $[One]) => d ** d }
    succeed
  }

  test("cosemigroupal variable: unused") {
    val e = intercept[Exception] {
      λ.+ { (_: $[One]) => one }
    }
    assert(e.getMessage `contains` "Unused variable")
    assert(e.getMessage `contains` "variable bound by lambda expression at")
    assert(e.getMessage `contains` "LambdaTests.scala:183")
  }

  test("cosemigroupal variable: used twice, with a twist") {
    λ.+ { (d: $[One]) =>
      val (p ** q) = dup(d)
      val (r ** s) = dup(d)
      (p ** r) ** (q ** s)
    }
    succeed
  }

  test("cosemigroupal variable: derived expressions remain linear") {
    val e = intercept[Exception] {
      λ.+ { (d: $[One]) =>
        val someExpensiveOrSideEffectingFunction = id[One]
        val x = someExpensiveOrSideEffectingFunction(d)
        x ** x
      }
    }
    assert(e.getMessage `contains` "used more than once")
    assert(e.getMessage `contains` "The result of function application")
    assert(e.getMessage `contains` "LambdaTests.scala:203")
  }

  test("comonoidal variable: used once") {
    λ.* { (p: $[One]) => p }
    succeed
  }

  test("comonoidal variable: used twice") {
    λ.* { (p: $[One]) => p ** p }
    succeed
  }

  test("comonoidal variable: unused") {
    λ.* { (_: $[One]) => one }
    succeed
  }

  test("introduce non-linearity via pattern match") {
    λ { (a: $[One]) =>
      a match
        case *(a) =>
          (a, a) match
            case (?(a0), a) =>
              a ** a
    }
    succeed
  }

  test("discard projection 1") {
    λ { (a: $[One ** One]) =>
      a match {
        case ?(_) ** a2 =>
          a2
      }
    }
    succeed
  }

  test("discard projection 2") {
    λ { (a: $[One ** One]) =>
      a match {
        case a1 ** ?(_) =>
          a1
      }
    }
    succeed
  }

  test("discard both projections") {
    λ { (a: $[One ** One]) =>
      a match
        case ?(_) ** ?(_) =>
          one
    }
    succeed
  }

  test("simple switch on ++") {
    λ { (a: $[One ++ One]) =>
      a switch {
        case Left(d)  => d
        case Right(d) => d
      }
    }
    succeed
  }

  test("nested switch on ++") {
    λ { (a: $[One ++ (One ++ One)]) =>
      a switch {
        case Left(d) => d
        case Right(e) =>
          e switch {
            case Left(d) => d
            case Right(d) =>
              val (d1 ** d2) = d > dup
              (d1 ** d2) > prj2
          }
      }
    }
    succeed
  }

  test("switch on ++ capturing outer variables") {
    λ { (a: $[Val[Int] ** (One ++ One)]) =>
      val a1 ** a2 = a
      a2 switch {
        case Left(u) =>
          (u ** neglect(a1)) > unliftPair
        case Right(u) =>
          (neglect(a1) ** u) > unliftPair
      }
    }
    succeed
  }

  test("switch with (multi-use) captured expression in one branch and no-use in the other branch") {
    λ { (x: $[One ** (One ++ One)]) =>
      x match
        case (*(a) ** b) =>
          b switch {
            case Left(d)  => d ** (a > neglect) ** (a > neglect) > prj1 > prj1 // `a` used twice
            case Right(d) => d // `a` unused
          }
    }
    succeed
  }
}
