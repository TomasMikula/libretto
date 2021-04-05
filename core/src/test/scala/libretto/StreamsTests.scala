package libretto

import scala.concurrent.duration._

class StreamsTests extends TestSuite {
  import kit.dsl._
  import kit.coreLib._
  import kit.coreStreams._
  import kit.scalaLib._

  val scalaStreams = ScalaStreams(kit.dsl, kit.coreLib, kit.scalaLib, kit.coreStreams)

  import scalaStreams._

  test("toList ⚬ fromList = id") {
    assertVal(
      done > Pollable.fromList(List(1, 2, 3, 4, 5, 6)) > Pollable.toList,
      List(1, 2, 3, 4, 5, 6),
    )
  }

  test("Pollable.map") {
    assertVal(
      done > Pollable.fromList(List(1, 2, 3)) > Pollable.map(_.toString) > Pollable.toList,
      List("1", "2", "3"),
    )
  }

  test("partition") {
    assertVal(
      done
        .>(Pollable.of(1, 2, 3, 4, 5, 6))
        .>(Pollable.map { i => if (i % 2 == 0) Left(i) else Right(i) })
        .>(Pollable.partition)
        .par(Pollable.toList, Pollable.toList)
        .>(unliftPair),
      (List(2, 4, 6), List(1, 3, 5)),
    )
  }

  test("concat") {
    assertVal(
      done
        .>(fork(Pollable.of(1, 2, 3), Pollable.of(4, 5, 6)))
        .>(Pollable.concat)
        .>(Pollable.toList),
      List(1, 2, 3 ,4, 5, 6),
    )
  }

  test("merge") {
    assertVal(
      parFromOne(
        done > Pollable.of(1, 2, 3),
        done > Pollable.of(4, 5, 6),
      )
        .>(Pollable.merge)
        .>(Pollable.toList)
        .>(mapVal(_.toSet)),
      Set(1, 2, 3, 4, 5, 6),
    )
  }

  test("mergeAll") {
    testVal(
      LList
        .of(
          done > Pollable.of(1, 2, 3),
          done > Pollable.of(4, 5, 6) > Pollable.delay(10.millis),
          done > Pollable.of(7, 8, 9),
        )
        .>(Pollable.mergeAll)
        .>(Pollable.toList)
    ) { (res: List[Int]) =>
      assert(res.toSet == Set(1, 2, 3, 4, 5, 6, 7, 8, 9))
      val (res1, res2) = res.splitAt(6)
      assert(res1.toSet == Set(1, 2, 3, 7, 8, 9))
      assert(res2 == List(4, 5, 6))
    }
  }

  test("broadcastByKey") {
    import Pollable.broadcastByKey
    import Pollable.BroadcastByKey.{close => closeBroadcast, subscribe}

    val byLength: Val[String] -⚬ (Val[Int] |*| Val[String]) =
      mapVal[String, (Int, String)](s => (s.length, s)) > liftPair

    val input: One -⚬ Pollable[String] =
      done > Pollable.of("f", "fo", "foo", "fooo", "foooo", "pho", "phoo", "phooo", "bo", "boo")

    val prg: One -⚬ Val[List[String]] =
      input
        .>(Pollable.delay(10.millis)) // delay so that subscribers have some time to subscribe
        .>(broadcastByKey(byLength))
        .>(subscribe(3))
        .>.fst(subscribe(4))
        .assocLR.>.snd(Pollable.merge)
        .par(closeBroadcast, Pollable.toList)
        .awaitFst

    assertVal(
      prg > mapVal(_.toSet),
      Set("foo", "fooo", "pho", "phoo", "boo"),
    )
  }
}
