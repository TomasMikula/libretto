package libretto.stream

import libretto.puro.PuroLib
import libretto.scaletto.ScalettoLib
import libretto.stream.puro.PuroStreams
import libretto.stream.scaletto.ScalettoStreams
import libretto.testing.TestCase
import libretto.testing.scaletto.ScalettoTestKit
import libretto.testing.scalatest.scaletto.ScalatestScalettoTestSuite
import scala.concurrent.duration.*

class StreamsTests extends ScalatestScalettoTestSuite {
  override def testCases(using kit: ScalettoTestKit): List[(String, TestCase[kit.type])] = {
    import kit.{Outcome, dsl}
    import kit.Outcome.{assertEquals, success}

    val puroLib = PuroLib(dsl)
    val scalettoLib = ScalettoLib(dsl: dsl.type, puroLib)
    val puroStreams = PuroStreams(dsl, puroLib)
    val scalettoStreams = ScalettoStreams(kit.dsl, puroLib, scalettoLib, puroStreams)

    import dsl.*
    import puroLib.*
    import scalettoLib.{*, given}
    import scalettoStreams.*

    List(
      "toList ⚬ fromList = id" -> TestCase
        .interactWith { ValSource.fromList(List(1, 2, 3, 4, 5, 6)) > ValSource.toList }
        .via { _.expectVal.flatMap(assertEquals(_, List(1, 2, 3, 4, 5, 6))) },

      "ValSource.map" -> TestCase
        .interactWith {
          ValSource.fromList(List(1, 2, 3)) > ValSource.map(_.toString) > ValSource.toList
        }.via {
          _.expectVal.flatMap(assertEquals(_, List("1", "2", "3")))
        },

      "partition" -> TestCase
        .interactWith {
          ValSource.of(1, 2, 3, 4, 5, 6)
            .>(ValSource.map { i => if (i % 2 == 0) Left(i) else Right(i) })
            .>(ValSource.partition)
            .>(par(ValSource.toList, ValSource.toList))
            .>(unliftPair)
        }.via {
          _.expectVal.flatMap(assertEquals(_, (List(2, 4, 6), List(1, 3, 5))))
        },

      "concat" -> TestCase
        .interactWith {
          forkMap(ValSource.of(1, 2, 3), ValSource.of(4, 5, 6))
            .>(ValSource.concat)
            .>(ValSource.toList)
        }.via {
          _.expectVal.flatMap(assertEquals(_, List(1, 2, 3 ,4, 5, 6)))
        },

      "merge" -> TestCase
        .interactWith {
          forkMap(
            ValSource.of(1, 2, 3),
            ValSource.of(4, 5, 6),
          )
            .>(ValSource.merge)
            .>(ValSource.toList)
            .>(mapVal(_.toSet))
        }.via {
          _.expectVal.flatMap(assertEquals(_, Set(1, 2, 3, 4, 5, 6)))
        },

      "mergeAll" -> TestCase
        .interactWith {
          LList1
            .of(
              ValSource.of(1, 2, 3),
              ValSource.of(4, 5, 6) > ValSource.delay(20.millis),
              ValSource.of(7, 8, 9),
            )
            .>(LList1.toLList)
            .>(ValSource.mergeAll)
            .>(ValSource.toList)
        }.via { port =>
          for {
            res <- port.expectVal
            _   <- assertEquals(res.toSet, Set(1, 2, 3, 4, 5, 6, 7, 8, 9))
            (res1, res2) = res.splitAt(6)
            _   <- assertEquals(res1.toSet, Set(1, 2, 3, 7, 8, 9))
            _   <- assertEquals(res2, List(4, 5, 6))
          } yield ()
        },

      "merge{Preferred, Balanced}" -> {
        val N = 100

        def mkTestCase(
          merge: (ValSource[String] |*| ValSource[String]) -⚬ ValSource[String],
          check: Int => kit.Outcome[Unit],
          slowConsumer: Boolean,
          slowedProducer1: Boolean,
        ): TestCase.Single[kit.type] =
          TestCase
            .interactWith {
              λ { case +(start) =>
                val as = start |> ValSource.fromList(List.fill(N)("a"))
                val as1 = if (slowedProducer1) as |> Source.mapSequentially(delayVal(3.millis)) else as
                val bs = start |> ValSource.fromList(List.fill(N)("b"))
                val cs = merge(as1 |*| bs)
                val cs1 = if (slowConsumer) cs |> Source.mapSequentially(delayVal(4.millis)) else cs
                cs1 |> ValSource.take(N) > ValSource.toList
              }
            }
            .via { port =>
              for {
                res <- port.expectVal
                n = res.count(_ == "a")
                _ <- check(n)
              } yield ()
            }

        def balanced(slowConsumer: Boolean) =
          mkTestCase(
            ValSource.mergeBalanced,
            n => Outcome.assert(n >= 0.4 * N && n <= 0.6 * N, s"$n out of $N elements come from the first source"),
            slowConsumer,
            slowedProducer1 = slowConsumer,
          )

        TestCase.multiple(
          "preferred" -> TestCase.multiple(
            "slow consumer" ->
              mkTestCase(
                ValSource.mergePreferred,
                n => Outcome.assert(n >= 0.9 * N, s"Only $n out of $N elements come from the first source"),
                slowConsumer = true,
                slowedProducer1 = true,
              ),
            "fast consumer" ->
              mkTestCase(
                ValSource.mergePreferred,
                n => Outcome.assert(n <= 0.5 * N, s"$n out of $N elements still come from the first source."),
                slowConsumer = false,
                slowedProducer1 = true,
              ),
          ),
          "balanced" -> TestCase.multiple(
            "slow consumer" -> balanced(slowConsumer = true),
            "fast consumer" -> balanced(slowConsumer = false),
          ),
        )
      },

      "dup" -> TestCase
        .interactWith {
          import ValSource.{dup, toList}

          λ { (start: $[Done]) =>
            val src = start |> ValSource.of(0, 1, 2, 3, 4, 5, 6, 7, 8, 9)
            val (out1 |*| out2) = dup(src)
            toList(out1) ** toList(out2)
          }
        }.via { port =>
          port.expectVal.flatMap { actual =>
            assertEquals(
              actual,
              expected = (
                List(0, 1, 2, 3, 4, 5, 6, 7, 8, 9),
                List(0, 1, 2, 3, 4, 5, 6, 7, 8, 9),
              )
            )
          }
        },

      "broadcastByKey" -> TestCase
        .interactWith {
          import ValSource.broadcastByKey
          import ValSource.BroadcastByKey.{close as closeBroadcast, subscribe}

          val byLength: Val[String] -⚬ (Val[Int] |*| Val[String]) =
            mapVal[String, (Int, String)](s => (s.length, s)) > liftPair

          val input: Done -⚬ ValSource[String] =
            ValSource.of("f", "fo", "foo", "fooo", "foooo", "pho", "phoo", "phooo", "bo", "boo")

          val prg: Done -⚬ Val[List[String]] =
            input
              .>(ValSource.delay(10.millis)) // delay so that subscribers have some time to subscribe
              .>(broadcastByKey(byLength))
              .>(subscribe(3))
              .>(fst(subscribe(4)))
              .>(assocLR).>(snd(ValSource.merge))
              .>(par(closeBroadcast, ValSource.toList))
              .>(awaitPosFst)

          prg > mapVal(_.toSet)
        }.via {
          _.expectVal.flatMap(assertEquals(_, Set("foo", "fooo", "pho", "phoo", "boo")))
        },

      "ValueDrain.contraDup pulls as soon as either one pulls" -> TestCase
        .interactWith {
          val prg: Done -⚬ (ValSource[Unit] |*| ValSource[Unit] |*| ValDrain[Unit]) =
            λ { start =>
              val (src1 |*| drn1) = $.one |> lInvertValSource[Unit]
              val (src2 |*| drn2) = $.one |> lInvertValSource[Unit]
              val drn = ValDrain.contraDup(drn1 |*| drn2)
              (src1 |*| src2) |*| (drn onCloseAwait start)
            }

          prg
        }
        .via { port =>
          val (srcs, drn)  = port.unzip()
          val (src1, src2) = srcs.unzip()
          val p1           = src1 append ValSource.poll
          for {
            pulling <- (drn append ValDrain.toEither).expectRight // checking pull before src2 acts
            // close everything
            _  = (pulling append ValDrain.Pulling.close append need).discardOne()
            d1 <- (src2 append ValSource.close).expectDone
            d2 <- (p1 append ValSource.Polled.close).expectDone
          } yield success(())
        },

      "prefetch" -> {
        val n = 10
        val N = 20
        TestCase.interactWith {
          val prg: Done -⚬ ((Pong |*| Done) |*| (Val[List[Int]] |*| Val[List[Int]])) =
            ValSource.fromList(List.range(0, N)) > ValSource.tap > par(
              ValSource.prefetch(n) > ValSource.delayable > par(strengthenPong, ValSource.close),
              LList.splitAt(n) > par(toScalaList, toScalaList),
            )
          prg
        }
        .via { port =>
          val (signals, outputs) = port.unzip()
          val (out1, out2) = outputs.unzip()
          val (pong, done) = signals.unzip()
          for {
            res1 <- out1.expectVal // the first n should be output before the first poll
            _ = pong.supplyPong()
            res2 <- out2.expectVal
            _ <- done.expectDone
            _ <- Outcome.assertAll(
              Outcome.assertEquals(res1, List.range(0, n)),
              Outcome.assertEquals(res2, List.empty),
            )
          } yield success(())
        }
      },

      "prefetch > flatten" -> {
        import java.util.concurrent.atomic.AtomicReference
        case class Counter(current: Int = 0, max: Int = 0) {
          def inc: Counter = Counter(current + 1, math.max(current + 1, max))
          def dec: Counter = Counter(current - 1, max)
        }

        val n = 4
        val N = 100

        val singletonAndCloseLater: Val[AtomicReference[Counter]] -⚬ ValSource[Unit] =
          dup > par(
            mapVal[AtomicReference[Counter], Unit](_ => ()),
            delayVal(5.millis) > mapVal[AtomicReference[Counter], Counter] { ref => ref.updateAndGet(_.dec) } > neglect,
          ) > ValSource.singleton

        val prg: Done -⚬ (Done |*| Val[AtomicReference[Counter]]) =
          constVal(new AtomicReference(Counter())) > λ { case +(counter) =>
            val done = counter
              |> ValSource.repeatedly(mapVal[AtomicReference[Counter], AtomicReference[Counter]] { ref => ref.updateAndGet(_.inc); ref })
              |> Source.map(singletonAndCloseLater)
              |> Source.prefetch(n - 1)(Source.close)
              |> Source.flatten
              |> ValSource.take(N)
              |> ValSource.forEachSequentially(neglect)
            done |*| counter
          }

        TestCase
          .interactWith(prg)
          .via { port =>
            val (done, ref) = port.unzip()
            for {
              _ <- done.expectDone
              ref <- ref.expectVal
              Counter(k, m) = ref.get()
              _ <- assertEquals(k, 0)
              _ <- assertEquals(m, n)
            } yield success(())
          }
      },
    )
  }
}
