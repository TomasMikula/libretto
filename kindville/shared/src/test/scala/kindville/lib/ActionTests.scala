package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class ActionTests extends AnyFunSuite {

  test("action of Function1 on Option") {
    val in = [A, B] => (oa: Option[A], f: A => B) => oa.map(f)

    val action: Action[* :: TNil, Option, Function1] =
      Action.pack[* :: TNil, Option, Function1](in)

    val out1 = Action.unpack(action)(Some("hello"), _.length())
    val out2 = action.act(Some("hello"), _.length())
    val out3 = action.actBy((_: String).length())(Some("hello"))
    val out4 = action.actOn(Some("hello"))((_: String).length())

    assert(out1 == Some(5))
    assert(out2 == Some(5))
    assert(out3 == Some(5))
    assert(out4 == Some(5))
  }

}
