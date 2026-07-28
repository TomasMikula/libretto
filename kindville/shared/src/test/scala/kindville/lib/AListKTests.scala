package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class AListKTests extends AnyFunSuite {

  test("list of functions") {
    val f: AListK[kindville.*, Function1, Int, Boolean] =
      (_.toString) ::
      ((_: String).split("0")) ::
      ((_: Array[String]).map(_.length)) ::
      ((_: Array[Int]).exists(_ % 2 == 0)) ::
      AListK.empty[*][Function1, Boolean]()

    // same as f, but using AListK.single as a starting point
    val g: AListK[kindville.*, Function1, Int, Boolean] =
      (_.toString) ::
      ((_: String).split("0")) ::
      ((_: Array[String]).map(_.length)) ::
      AListK.single[*]((_: Array[Int]).exists(_ % 2 == 0))

    type Id[A] = A
    val in: App[kindville.*, Id, Int] =
      App.packer[*](504030201)
    val action: Action[kindville.*, Id, Function1] =
      Action.pack[*, Id, Function1]([A, B] => (a: A, f: A => B) => f(a))

    val out1 = f.foldLeft[Id](in, action).unpack
    val out2 = g.foldLeft[Id](in, action).unpack

    assert(out1 == false)
    assert(out2 == false)
  }

  test("list of natural transformations") {
    type ~>[F[_], G[_]] = [X] => F[X] => G[X]
    type OfInt[F[_]] = F[Int]

    val f: AListK[* -> *, ~>, List, Option] =
      // ([X] => (xs: List[X]) => xs.reverse) ::
      ([X] => (xs: List[X]) => xs.headOption) ::
      AListK.empty[* -> *][~>, Option]()

    val action: Action[* -> *, OfInt, ~>] =
      Action.pack[* -> *, OfInt, ~>]([F[_], G[_]] => (a: F[Int], f: F ~> G) => f(a))

    val in: App[* -> *, OfInt, List] =
      App.packer[* -> *](List(1, 2, 3))

    val out = f.foldLeft[OfInt](in, action)

    assert(out.unpack == Some(1))
  }
}
