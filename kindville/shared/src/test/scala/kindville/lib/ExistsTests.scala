package kindville.lib

import org.scalatest.funsuite.AnyFunSuite
import scala.annotation.experimental

@experimental
class ExistsTests extends AnyFunSuite {

  test("Exists[[P, Q] =>> (String => P, P => Q, Q => Int)]") {
    val x: Exists[[P, Q] =>> (String => P, P => Q, Q => Int)] =
      Exists[[P, Q] =>> (String => P, P => Q, Q => Int)]
        .apply[Array[String], Array[Int]]((
          _.split("\\."),
          _.map(_.length),
          _.fold(0)(_ + _),
        ))

    val visit = x.visit
    val n =
      visit[Int] { [P, Q] => (fgh: (String => P, P => Q, Q => Int)) =>
        val (f, g, h) = fgh
        h(g(f("hello.kindville.citizens")))
      }

    assert(n == 22)
  }

}
