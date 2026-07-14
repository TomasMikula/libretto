package kindville

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class EncodingTests extends AnyFunSuite {

  test("decode([⋅⋅[_]] => _ ?=> 0)") {
    val x = decode([⋅⋅[_]] => _ ?=> 0)
    assert(x == 0)
  }

  test("decodeT[List :: TNil]([⋅⋅[_]] => kuotes ?=> [F[_]] => () => 0)") {
    val x = decodeT[List :: TNil]([⋅⋅[_]] => kuotes ?=> [F[_]] => () => 0)
    assert(x == 0)
  }

  test("decodeT[List :: Int :: TNil]([⋅⋅[_]] => _ ?=> [F[_], A] => () => (fa: F[A]) => fa)") {
    val id: List[Int] => List[Int] =
      decodeT[List :: Int :: TNil]([⋅⋅[_]] => _ ?=> [F[_], A] => () => (fa: F[A]) => fa)
    assert(id(List(1, 2, 3)) == List(1, 2, 3))
  }

  test("decodeT[List :: Option :: Int :: TNil]([⋅⋅[_]] => _ ?=> [F[_], G[_], A] => () => (fa: F[A], ga: G[A]) => fa)") {
    val fst: (List[Int], Option[Int]) => List[Int] =
      decodeT[List :: Option :: Int :: TNil]([⋅⋅[_]] => _ ?=> [F[_], G[_], A] => () => (fa: F[A], ga: G[A]) => fa)
    assert(fst(List(1, 2, 3), Some(4)) == List(1, 2, 3))
  }

  test("decodeT[List :: Option :: Int :: TNil]([⋅⋅[_]] => k ?=> [F[_], G[_], A] => () => (fa: F[A], f: F[A] => G[A]) => f(fa))") {
    val go: (List[Int], List[Int] => Option[Int]) => Option[Int] =
      decodeT[List :: Option :: Int :: TNil]([⋅⋅[_]] => k ?=> [F[_], G[_], A] => () => (fa: F[A], f: F[A] => G[A]) => f(fa))
    assert(go(List(1, 2, 3), _.headOption) == Some(1))
  }

  test("locallyEquals[Option :: Int :: TNil, A]") {
    case class Foo[F[_], A](value: F[A])
    type K = (* -> *) :: * :: TNil

    decodeT[Foo :: (Option :: Int :: TNil) :: TNil]:
      [⋅⋅[_]] => k ?=> [F[_ <: ⋅⋅[K]], A <: ⋅⋅[K]] => () =>
        k.locallyEquals[Option :: Int :: TNil, A]: (Option :: Int :: TNil) =~= ⋅⋅[A]
  }

}
