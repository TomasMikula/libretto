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

  test("list of polymorphic functions") {
    type ~>[F[_], G[_]] = [X] => F[X] => G[X]
    type OfInt[F[_]] = F[Int]

    val reverse: List ~> List = [X] => _.reverse
    val headOpt: List ~> Option = [X] => _.headOption

    val f: AListK[* -> *, ~>, List, Option] =
      headOpt ::
      AListK.empty[* -> *][~>, Option]()

    val g: AListK[* -> *, ~>, List, Option] =
      reverse :: f

    val action1: Action[* -> *, OfInt, ~>] =
      Action.pack[* -> *, OfInt, ~>]([F[_], G[_]] => (a: F[Int], f: F ~> G) => f(a))
    val action2: Action[* -> *, OfInt, ~>] = // same as action1, just using `packer` to create
      Action.packer[* -> *][OfInt, ~>]([F[_], G[_]] => (a: F[Int], f: F ~> G) => f(a))

    val in: App[* -> *, OfInt, List] =
      App.packer[* -> *](List(1, 2, 3))

    val fOut1 = f.foldLeft[OfInt](in, action1)
    val fOut2 = f.foldLeft[OfInt](in, action2)
    val gOut1 = g.foldLeft[OfInt](in, action1)
    val gOut2 = g.foldLeft[OfInt](in, action2)

    assert(fOut1.unpack == Some(1))
    assert(fOut2.unpack == Some(1))
    assert(gOut1.unpack == Some(3))
    assert(gOut2.unpack == Some(3))
  }

  test("list of multi-parameter arrows") {
    trait Functor[F[_]]:
      def map[A](fa: F[A])[B](f: A => B): F[B]

    // An arrow type whose input and output are two type parameters each, F, A and G, B, respectively.
    // NB, it's a rather boring one, composed of two independent functions, but fits the bill of multi-param arrow.
    case class Arr[A, F[_], B, G[_]](
      f: A => B,
      g: [X] => F[X] => G[X],
      G: Functor[G],
    )

    case class EitherT[L, F[_], R](value: F[Either[L, R]]) {
      def translate[M, G[_]](arr: Arr[L, F, M, G]): EitherT[M, G, R] =
        EitherT(arr.G.map(arr.g(value))(_.left.map(arr.f)))
    }

    // Action of Arr on EitherT
    def translatorAction[T]: Action[* :: (* -> *) :: TNil, [A, F[_]] =>> EitherT[A, F, T], Arr] =
      Action.packer[* :: (* -> *) :: TNil][[A, F[_]] =>> EitherT[A, F, T], Arr](
        [A, F[_], B, G[_]] => (x: EitherT[A, F, T], f: Arr[A, F, B, G]) => x.translate(f)
      )

    // Funtor instances
    val functorList: Functor[List] =
      new Functor[List]:
        override def map[A](as: List[A]) [B](f: A => B): List[B] = as.map(f)
    val functorOption: Functor[Option] =
      new Functor[Option]:
        override def map[A](ma: Option[A])[B](f: A => B): Option[B] = ma.map(f)

    // Arr instances
    val lengthsAndReverse: Arr[String, List, Int, List] =
      Arr(_.length, [X] => _.reverse, functorList)
    val oddsAndHeadOpt: Arr[Int, List, Boolean, Option] =
      Arr(_ % 2 == 1, [X] => _.headOption, functorOption)

    // chained Arr instances
    val f: AListK[* :: (* -> *) :: TNil, Arr, String :: List :: TNil, Boolean :: Option :: TNil] =
      lengthsAndReverse ::
      oddsAndHeadOpt ::
      AListK.empty[* :: (* -> *) :: TNil][Arr, Boolean, Option]()

    val in: App[* :: (* -> *) :: TNil, [A, F[_]] =>> EitherT[A, F, Unit], String :: List :: TNil] =
      App.packer[* :: (* -> *) :: TNil](EitherT(List(Left("1"), Left("four"))))

    val out: EitherT[Boolean, Option, Unit] =
      f.foldLeft(in, translatorAction[Unit]).unpack

    assert(out == EitherT(Some(Left(false))))
  }
}
