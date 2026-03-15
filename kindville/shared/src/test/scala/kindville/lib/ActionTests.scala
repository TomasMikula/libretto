package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class ActionTests extends AnyFunSuite {

  test("action of Function1 on Option") {
    val action: Action[* :: TNil, Option, Function1] =
      Action.pack[* :: TNil, Option, Function1]:
        [A, B] => (oa: Option[A], f: A => B) => oa.map(f)

    val actionRaw =
      Action.unpack(action)

    val n = actionRaw(Some("hello"), _.length())
    assert(n == Some(5))

    val m = action.act(Some("hello"), _.length())
    assert(m == Some(5))
  }

}
