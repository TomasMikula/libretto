package libretto.zio_interop

import libretto.examples.sunflowers
import libretto.examples.sunflowers.{OilBottle, SeedsPack, Sunflower, SunflowerProcessingFacility}
import libretto.zio_interop.OutPort.|*|
import zio.{Scope, ZIO}
import zio.stream.{UStream, ZStream}
import zio.test.{Assertion, Spec, TestEnvironment, ZIOSpecDefault, assert}

object SunflowersSpec extends ZIOSpecDefault {

  def go(
    sunflowers: UStream[Sunflower],
  ): ZIO[Scope, Nothing, (UStream[SeedsPack], UStream[OilBottle])] = {
    // prepare a description of ZIO input
    sunflowers.asSource
      // pass it through a Libretto function
      .through_(SunflowerProcessingFacility.blueprint)
      // convert the output back to ZIO
      .map { case oilBottles |*| seedPacks =>
        (oilBottles.zstream, seedPacks.zstream)
      }
  }

  override def spec: Spec[TestEnvironment & Scope, Any] =
    suite("Sunflowers suite")(
      test("produces the expected number of outputs") {
        val N = 1000

        go(
          ZStream.fromIterable(List.fill(N)(Sunflower())),
        )
          .flatMap { case (oils, seedss) =>
            (oils mergeEither seedss)
              .runFold(0) { (acc, elem) =>
                elem match
                  case Left(SeedsPack())  => acc + 3
                  case Right(OilBottle()) => acc + 5
              }
          }
          .map { n => assert(n)(Assertion.isGreaterThanEqualTo(N - 4)) }
      },
    )
}
