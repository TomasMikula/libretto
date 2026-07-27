package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class ActionTests extends AnyFunSuite {

  test("action of Function1 on Option") {
    val actionRaw = [A, B] => (oa: Option[A], f: A => B) => oa.map(f)

    val action: Action[kindville.*, Option, Function1] =
      Action.pack[*, Option, Function1](actionRaw)

    val strOpt: App[kindville.*, Option, String] =
      App.packer[*](Some("hello"))

    val strToInt: Arrow[kindville.*, Function1, String, Int] =
      Arrow.packer[*](_.length())

    val out1 = action.unpack(Some("hello"), _.length())
    val out2 = action.act(Some("hello"), _.length())
    val out3 = action.actBy((_: String).length())(Some("hello"))
    val out4 = action.actOn(Some("hello"))(_.length())
    val out5 = action(strOpt, strToInt).unpack
    val out6 = action.applyDynamic[String, Int](strOpt, strToInt).unpack

    assert(out1 == Some(5))
    assert(out2 == Some(5))
    assert(out3 == Some(5))
    assert(out4 == Some(5))
    assert(out5 == Some(5))
    assert(out6 == Some(5))
  }

  test("applyOpt of Function1 on Option") {
    val actionRaw = [A, B] => (oa: Option[A], f: A => B) => oa.map(f)

    val action: Action[kindville.*, Option, Function1] =
      Action.pack[*, Option, Function1](actionRaw)

    val intOpt: App[kindville.*, Option, Int] =
      App.packer[*](Some(1))

    val intToInt1: Arrow.Opt[kindville.*, Function1, Int, Int] =
      Arrow.Opt.Some(Arrow.packer[*](_ * 2))

    val intToInt2: Arrow.Opt[kindville.*, Function1, Int, Int] =
      Arrow.Opt.None()

    val out1 = action.applyOpt(intOpt, intToInt1).unpack
    val out2 = action.applyOpt(intOpt, intToInt2).unpack

    assert(out1 == Some(2))
    assert(out2 == Some(1))
  }

  test("action of polymorphic function on custom higher-kinded data type Foo[F[_]]") {
    type ~>[F[_], G[_]] = [A] => F[A] => G[A]

    case class Foo[F[_]](value: F[Int])

    val in: App[* -> *, Foo, List] =
      App.pack[* -> *, Foo, List](Foo(List(1, 2, 3)))
    val action: Action[* -> *, Foo, ~>] =
      Action.pack[* -> *, Foo, ~>]([F[_], G[_]] => (x, f) => Foo(f(x.value)))
    val headOptionArrow: Arrow[* -> *, ~>, List, Option] =
      Arrow.packer[* -> *]([A] => _.headOption)

    val out1 = action.act(Foo(List(1, 2, 3)), [A] => _.headOption)
    val out2 = action.actOn(Foo(List(1, 2, 3)))([A] => _.headOption)
    val out3 = action.actBy[List, Option]([A] => (as: List[A]) => as.headOption)(Foo(List(1, 2, 3)))
    val out4 = action(in, headOptionArrow).unpack
    val out5 = action.applyDynamic[List, Option](in, headOptionArrow).unpack

    assert(out1 == Foo(Some(1)))
    assert(out2 == Foo(Some(1)))
    assert(out3 == Foo(Some(1)))
    assert(out4 == Foo(Some(1)))
    assert(out5 == Foo(Some(1)))
  }

}
