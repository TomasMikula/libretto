package libretto

import libretto.scaletto.StarterKit.dsl.*
import org.scalatest.funsuite.AnyFunSuite

class ProgramSizeTests extends AnyFunSuite {

  test("reused part is smaller than inlined") {
    val part: Done -⚬ Done =
      fork > swap > join

    val prg0: Done -⚬ Done =
      fork > par(part, part) > join

    val prg1: Done -⚬ Done =
      val pt = sharedCode(part)
      fork > par(pt, pt) > join

    val s0 = sizeOf(prg0)
    val s1 = sizeOf(prg1)
    val expectedDiff = sizeOf(part) - 2

    assert(s1 < s0)
    assert(s0 - s1 == expectedDiff)
  }

}
