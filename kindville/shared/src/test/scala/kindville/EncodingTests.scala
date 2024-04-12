package kindville

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class EncodingTests extends AnyFunSuite {

  test("decodeExpr[TNil]([⋅⋅[_]] => (_: Unit) => 0)") {
    val x = decodeExpr[TNil]([⋅⋅[_]] => (_: Unit) => 0)(())
    assert(x == 0)
  }

  test("decodeExpr[List :: TNil]([⋅⋅[_], F[_]] => (_: Unit) => 0)") {
    val x = decodeExpr[List :: TNil]([⋅⋅[_], F[_]] => (_: Unit) => 0)(())
    assert(x == 0)
  }

  test("decodeExpr[List :: Int :: TNil]([⋅⋅[_], F[_], A] => (_: Unit) => (fa: F[A]) => fa)") {
    val id: List[Int] => List[Int] =
      decodeExpr[List :: Int :: TNil]([⋅⋅[_], F[_], A] => (_: Unit) => (fa: F[A]) => fa)(())
    assert(id(List(1, 2, 3)) == List(1, 2, 3))
  }

  test("decodeExpr[Option :: Int :: TNil]([⋅⋅[_], F[_], A] => (fa: F[A]) => fa)") {
    val x: Option[Int] =
      decodeExpr[Option :: Int :: TNil]([⋅⋅[_], F[_], A] => (fa: F[A]) => fa)(Some(1))
    assert(x == Some(1))
  }

  test("decodeExpr[List :: List :: Int :: TNil]([⋅⋅[_], F[_], G[_], A] => (fa: F[A], ga: G[A]) => fa)") {
    val x: List[Int] =
      decodeExpr[List :: List :: Int :: TNil]([⋅⋅[_], F[_], G[_], A] => (fa: F[A], ga: G[A]) => fa)(List(1, 2, 3), List(4))
    assert(x == List(1, 2, 3))
  }

  test("decodeExpr[List :: Option :: Int :: TNil]([⋅⋅[_], F[_], G[_], A] => (_: Unit) => (fa: F[A], ga: G[A]) => fa)") {
    val fst: (List[Int], Option[Int]) => List[Int] =
      decodeExpr[List :: Option :: Int :: TNil]([⋅⋅[_], F[_], G[_], A] => (_: Unit) => (fa: F[A], ga: G[A]) => fa)(())
    assert(fst(List(1, 2, 3), Some(4)) == List(1, 2, 3))
  }

  test("decodeExpr[List :: Option :: Int :: TNil]([⋅⋅[_], F[_], G[_], A] => (_: Unit) => (fa: F[A], f: F[A] => G[A]) => f(fa))") {
    val go: (List[Int], List[Int] => Option[Int]) => Option[Int] =
      decodeExpr[List :: Option :: Int :: TNil]([⋅⋅[_], F[_], G[_], A] => (_: Unit) => (fa: F[A], f: F[A] => G[A]) => f(fa))(())
    assert(go(List(1, 2, 3), _.headOption) == Some(1))
  }

  test("decodeFun([⋅⋅[_], F[_], G[_], A] => (fa: F[A], f: F[A] => G[A]) => f(fa))") {
    val go: [F[_], G[_], A] => (F[A], F[A] => G[A]) => G[A] =
      decodeFun([⋅⋅[_], F[_], G[_], A] => (fa: F[A], f: F[A] => G[A]) => f(fa))

    assert(go(List(1, 2, 3), _.headOption) == Some(1))
  }

  test("decodeFun([⋅⋅[_], F[_ <: ⋅⋅[K]], A <: ⋅⋅[K]] => (fa: F[A]) => fa)") {
    type K = * :: * :: TNil

    val go: [F[_, _], A, B] => F[A, B] => F[A, B] =
      decodeFun([⋅⋅[_], F[_ <: ⋅⋅[K]], A <: ⋅⋅[K]] => (fa: F[A]) => fa)

    assert(go(Map(1 -> "a")) == Map(1 -> "a"))
  }

  test("decodeFun([⋅⋅[_], G[F[_ <: ⋅⋅[K]]], F[_ <: ⋅⋅[K]]] => (gf: G[F]) => gf)") {
    type K = * :: * :: TNil

    val go: [G[F[_, _]], F[_, _]] => G[F] => G[F] =
      decodeFun([⋅⋅[_], G[F[_ <: ⋅⋅[K]]], F[_ <: ⋅⋅[K]]] => (gf: G[F]) => gf)

    case class Foo[F[_, _]](f1: F[String, Int], f2: F[Int, Boolean])

    val foo = Foo[Function1](_.length, i => (i % 2) == 0)
    val bar = go(foo)
    assert(bar == foo)
  }

}
