package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class ExistsTests extends AnyFunSuite {

  test("ExistK[* :: TNil, [X] =>> Option[X]") {
    val x: ExistK[* :: TNil, Option] =
      ExistK[* :: TNil, [X] =>> Option[X]](Some(1))

    val s =
      x.visit[String] { [T] => (ot: Option[T]) =>
        ot.toString
      }

    assert(s == "Some(1)")
  }

  test("ExistK[* :: * :: TNil, [P, Q] =>> (String => P, P => Q, Q => Int)]") {
    val x: ExistK[* :: * :: TNil, [P, Q] =>> (String => P, P => Q, Q => Int)] =
      ExistK[* :: * :: TNil, [P, Q] =>> (String => P, P => Q, Q => Int)]
        .apply[Array[String], Array[Int]]((
          _.split("\\."),
          _.map(_.length),
          _.sum,
        ))

    val visit = x.visit
    val n =
      visit[Int] { [P, Q] => (fgh: (String => P, P => Q, Q => Int)) =>
        val (f, g, h) = fgh
        h(g(f("hello.kindville.citizens")))
      }

    assert(n == 22)
  }

  test("Inferrability of: existential arguments at creation, result type of visit") {
    val f: String        => Array[String] = _.split("\\.")
    val g: Array[String] => Array[Int]    = _.map(_.length)
    val h: Array[Int]    => Int           = _.sum

    val x: ExistK[* :: * :: TNil, [P, Q] =>> (String => P, P => Q, Q => Int)] =
      // Not specifying arguments for P, Q explicitly.
      // They are inferred to be Array[String], Array[Int], respectively.
      ExistK[* :: * :: TNil, [P, Q] =>> (String => P, P => Q, Q => Int)]((f, g, h))

    val n =
      // Not specifying result type of visit explicitly.
      // It is inferred to be Int.
      x.visit { [P, Q] => (fgh: (String => P, P => Q, Q => Int)) =>
          val (f, g, h) = fgh
          h(g(f("hello.kindville.citizens")))
        }

    assert(n == 22)
  }

  test("Inferrability of the result type F[A, ...]") {
    ExistK.types[String :: Int :: TNil]
      .suchThat[* :: * :: TNil, Map[_, _]](Map.empty) // inferred type Map[String, Int]

    // Proof:
    // Let the type of `x` be inferred
    val x =
      ExistK.types[String :: Int :: TNil]
        .suchThat[* :: * :: TNil, Map[_, _]]

    // The inferred type is assignable to `Map[String, Int] => Exists[Map]`
    val y: Map[String, Int] => ExistK[* :: * :: TNil, Map] =
      x
  }

}
