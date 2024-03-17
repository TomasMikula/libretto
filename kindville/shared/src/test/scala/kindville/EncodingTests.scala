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

}
