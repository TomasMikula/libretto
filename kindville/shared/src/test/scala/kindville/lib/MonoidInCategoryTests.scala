package kindville.lib

import org.scalatest.funsuite.AnyFunSuite

class MonoidInCategoryTests extends AnyFunSuite {

  test("Monoid[Int] is a monoid in the category of types and functions") {
    val monoid = Monoid[Int](
      unit = 0,
      combine = _ + _,
    )

    assert(monoid.unit(()) == 0)
    assert(monoid.combine(3, 4) == 7)
  }

  test("Monad[Option] is a monoid in the category of endofunctors") {
    val functorOption: Functor[Option] =
      new Functor[Option]:
        def map[A, B](f: A => B): Option[A] => Option[B] =
          _.map(f)

    val pure: Id ~> Option =
      [A] => (a: A) => Some(a)

    val flatten: (Option ∘ Option) ~> Option =
      [A] => (ooa: Option[Option[A]]) => ooa.flatten

    val monad = Monad[Option](
      functor = functorOption,
      pure = pure,
      flatten = flatten,
    )

    assert(monad.pure[Int](1) == Some(1))
    assert(monad.flatten[Int](Some(Some(1))) == Some(1))
    assert(monad.flatten[Int](Some(None)) == None)
  }

  test("Applicative[Option] is a monoid in the functor category with Day convolution") {
    import scala.:: as NonEmptyList

    enum Validated[A]:
      case Valid(value: A)
      case Invalid(errors: NonEmptyList[String])

    import Validated.*

    def invalid[A](s: String): Validated[A] = Invalid(NonEmptyList(s, Nil))

    val pure: Id ~> Validated =
      [A] => (a: A) => Valid(a)

    val ap: DayConv[Validated, Validated] ~> Validated =
      [A] => (day: Day[Validated, Validated, A]) =>
        (day.fx, day.gy) match
          case (Valid(x), Valid(y)) => Valid(day.f(x, y))
          case (Valid(_), Invalid(fs)) => Invalid(fs)
          case (Invalid(es), Valid(_)) => Invalid(es)
          case (Invalid(e :: es), Invalid(fs)) => Invalid(NonEmptyList(e, es ::: fs))

    val applicative = Applicative[Validated](
      pure = pure,
      ap = ap,
    )

    assert(applicative.pure[Int](1) == Valid(1))
    assert(applicative.ap(Valid((x: Int) => x + 1), Valid(1)) == Valid(2))
    assert(applicative.ap(Valid((x: Int) => x + 1), invalid("bad")) == invalid("bad"))
    assert(applicative.ap(invalid("bad"), Valid(1)) == invalid("bad"))
    assert(applicative.map(Valid(1))(_ + 1) == Valid(2))
  }

}
