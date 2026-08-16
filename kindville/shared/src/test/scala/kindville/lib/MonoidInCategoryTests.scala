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

}
