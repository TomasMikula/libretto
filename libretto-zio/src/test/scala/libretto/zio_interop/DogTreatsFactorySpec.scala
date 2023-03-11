package libretto.zio_interop

import libretto.examples.dogTreatsFactory
import zio.{Scope, ZIO}
import zio.stream.{UStream, ZStream}
import zio.test.{Assertion, Spec, TestEnvironment, ZIOSpecDefault, assert}

object DogTreatsFactorySpec extends ZIOSpecDefault {
  import dogTreatsFactory.{Biscuit, Bone, DogTreatsFactory, Toy, TreatsPack}

  def go(
    toys: UStream[Toy],
    bones: UStream[Bone],
    biscuits: UStream[Biscuit],
  ): ZIO[Scope, Nothing, UStream[TreatsPack]] = {
    // prepare a description of ZIO inputs
    (toys.asSource |*| bones.asSource |*| biscuits.asSource)
      // pass it through a Libretto function
      .through_(DogTreatsFactory.blueprint)
      // convert the output back to ZIO
      .map(_.zstream)
  }

  override def spec: Spec[TestEnvironment & Scope, Any] =
    suite("DogTreatsFactory suite")(
      test("produces the expected number of packs") {
        import dogTreatsFactory.Main.{inBiscuits, inBones, inToys, nToys}

        go(
          ZStream.fromIterable(inToys),
          ZStream.fromIterable(inBones),
          ZStream.fromIterable(inBiscuits),
        )
          .flatMap(_.runCollect)
          .map { packs => assert(packs.length)(Assertion.equalTo(nToys)) }
      },
    )
}
