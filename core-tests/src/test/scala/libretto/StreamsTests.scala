package libretto

import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.{ScalettoLib, ScalettoStreams}
import libretto.testing.{TestCase}
import libretto.testing.scaletto.ScalettoTestKit
import libretto.testing.scalatest.scaletto.ScalatestScalettoTestSuite
import scala.concurrent.duration._

class StreamsTests extends ScalatestScalettoTestSuite {
  override def testCases(using kit: ScalettoTestKit): List[(String, TestCase[kit.type])] = {
    import kit.{dsl, expectVal}
    import kit.dsl._
    import kit.Outcome.assertEquals

    val coreLib = CoreLib(dsl)
    val scalettoLib = ScalettoLib(dsl: dsl.type, coreLib)
    val coreStreams = CoreStreams(dsl, coreLib)
    val scalettoStreams = ScalettoStreams(kit.dsl, coreLib, scalettoLib, coreStreams)

    import coreLib._
    import scalettoLib._
    import scalettoStreams._

    List(
      "toList ⚬ fromList = id" -> TestCase
        .interactWith { Pollable.fromList(List(1, 2, 3, 4, 5, 6)) > Pollable.toList }
        .via { expectVal(_).assertEquals(List(1, 2, 3, 4, 5, 6)) },

      "Pollable.map" -> TestCase
        .interactWith {
          Pollable.fromList(List(1, 2, 3)) > Pollable.map(_.toString) > Pollable.toList
        }.via {
          expectVal(_).assertEquals(List("1", "2", "3"))
        },

      "partition" -> TestCase
        .interactWith {
          Pollable.of(1, 2, 3, 4, 5, 6)
            .>(Pollable.map { i => if (i % 2 == 0) Left(i) else Right(i) })
            .>(Pollable.partition)
            .par(Pollable.toList, Pollable.toList)
            .>(unliftPair)
        }.via {
          expectVal(_).assertEquals((List(2, 4, 6), List(1, 3, 5)))
        },

      "concat" -> TestCase
        .interactWith {
          forkMap(Pollable.of(1, 2, 3), Pollable.of(4, 5, 6))
            .>(Pollable.concat)
            .>(Pollable.toList)
        }.via {
          expectVal(_).assertEquals(List(1, 2, 3 ,4, 5, 6))
        },

      "merge" -> TestCase
        .interactWith {
          forkMap(
            Pollable.of(1, 2, 3),
            Pollable.of(4, 5, 6),
          )
            .>(Pollable.merge)
            .>(Pollable.toList)
            .>(mapVal(_.toSet))
        }.via {
          expectVal(_).assertEquals(Set(1, 2, 3, 4, 5, 6))
        },

      "mergeAll" -> TestCase
        .interactWith {
          LList1
            .of(
              Pollable.of(1, 2, 3),
              Pollable.of(4, 5, 6) > Pollable.delay(10.millis),
              Pollable.of(7, 8, 9),
            )
            .>(LList1.toLList)
            .>(Pollable.mergeAll)
            .>(Pollable.toList)
        }.via { port =>
          for {
            res <- expectVal(port)
            _   <- assertEquals(res.toSet, Set(1, 2, 3, 4, 5, 6, 7, 8, 9))
            (res1, res2) = res.splitAt(6)
            _   <- assertEquals(res1.toSet, Set(1, 2, 3, 7, 8, 9))
            _   <- assertEquals(res2, List(4, 5, 6))
          } yield ()
        },

      "broadcastByKey" -> TestCase
        .interactWith {
          import Pollable.broadcastByKey
          import Pollable.BroadcastByKey.{close => closeBroadcast, subscribe}

          val byLength: Val[String] -⚬ (Val[Int] |*| Val[String]) =
            mapVal[String, (Int, String)](s => (s.length, s)) > liftPair

          val input: Done -⚬ Pollable[String] =
            Pollable.of("f", "fo", "foo", "fooo", "foooo", "pho", "phoo", "phooo", "bo", "boo")

          val prg: Done -⚬ Val[List[String]] =
            input
              .>(Pollable.delay(10.millis)) // delay so that subscribers have some time to subscribe
              .>(broadcastByKey(byLength))
              .>(subscribe(3))
              .>.fst(subscribe(4))
              .assocLR.>.snd(Pollable.merge)
              .par(closeBroadcast, Pollable.toList)
              .awaitFst

          prg > mapVal(_.toSet)
        }.via {
          expectVal(_).assertEquals(Set("foo", "fooo", "pho", "phoo", "boo"))
        },
    )
  }
}
