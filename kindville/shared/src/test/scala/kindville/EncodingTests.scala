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

  test("decoding higher kinded type parameters of a polymorphic function") {
    val f = decode([⋅⋅[_]] => k ?=> [F[_ <: ⋅⋅[* -> *]], A <: ⋅⋅[* -> *]] => (fa: F[A]) => (fa: F[A]))
    // check that the decoded expression has the expected type
    f: ([F[_[_]], A[_]] => F[A] => F[A])

    // same as `f`, but with kinds of type params defined differently (but equivalently)0
    val g = decode([⋅⋅[_]] => k ?=> [F[_[_ <: ⋅⋅[kindville.*]]], A[_ <: ⋅⋅[kindville.*]]] => (fa: F[A]) => fa)
    // check that the decoded expression has the expected type
    g: ([F[_[_]], A[_]] => F[A] => F[A])

    // test usage of a type parameter (F) both as a type constructor (F[A]) and as a type argument (H[F])
    type K = * -> *
    val h = decode([⋅⋅[_]] => k ?=> [H[_[_ <: ⋅⋅[K]]], F[_ <: ⋅⋅[K]], A <: ⋅⋅[K]] => (hf: H[F], fa: F[A]) => (fa, hf))
    // check that the decoded expression has the expected type
    h: ([H[_[_[_]]], F[_[_]], A[_]] => (H[F], F[A]) => (F[A], H[F]))

    case class OfInt[F[_]](value: F[Int])
    case class OfOption[F[_[_]]](value: F[Option])
    assert(h(OfOption(OfInt(Option(1))), OfInt(Option(2))) == (OfInt(Some(2)), OfOption(OfInt(Some(1)))))
  }

  test("decodeT with higher-kinded type arguments, one of which is used both as type argument and as type constructor") {
    type ● = kindville.*

    trait Functor[F[_]]:
      extension [A](fa: F[A]) def map[B](f: A => B): F[B]
    object Functor:
      given Functor[Option] with
        extension [A](fa: Option[A]) override def map[B](f: A => B): Option[B] = fa.map(f)

    case class EitherT[L, F[_], R](value: F[Either[L, R]])
    object EitherT {
      def liftF[L, F[_]: Functor, A](fa: F[A]): EitherT[L, F, A] = EitherT(fa.map(Right(_)))
    }

    val mkLiftOptionInt =
      decodeT[([F[_], A] =>> EitherT[String, F, A]) :: Option :: Int :: TNil]:
        [⋅⋅[_]] => k ?=> [H[_[_ <: ⋅⋅[●]], _ <: ⋅⋅[●]], F[_ <: ⋅⋅[●]], A <: ⋅⋅[●]] => () =>
          // note that F is used both as type argument (in H[F, X]) and type constructor (in F[A])
          (liftF: [X <: ⋅⋅[●]] => F[X] => H[F, X]) => (fa: F[A]) => (liftF(fa): H[F, A])

    // check that the decoded expression has the expected type
    mkLiftOptionInt: ((liftF: [X] => Option[X] => EitherT[String, Option, X]) => Option[Int] => EitherT[String, Option, Int])

    val liftOptionInt: (Option[Int] => EitherT[String, Option, Int]) =
      mkLiftOptionInt([X] => EitherT.liftF[String, Option, X](_))

    assert(liftOptionInt(Some(0)).value == Some(Right(0)))
  }

}
