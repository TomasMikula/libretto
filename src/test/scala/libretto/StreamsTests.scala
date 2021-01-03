package libretto

class StreamsTests extends TestSuite {
  import kit.dsl._
  import kit.coreLib._
  import kit.scalaLib._
  
  val scalaStreams = ScalaStreams(kit.dsl, kit.coreLib, kit.scalaLib, kit.coreStreams)
  
  import scalaStreams._
  
  test("toList ⚬ fromList = id") {
    assertResult(
      Pollable.fromList(List(1, 2, 3, 4, 5, 6)) >>> Pollable.toList,
      List(1, 2, 3, 4, 5, 6),
    )
  }
}
