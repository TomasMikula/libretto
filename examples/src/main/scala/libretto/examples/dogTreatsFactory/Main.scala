package libretto.examples.dogTreatsFactory

import libretto.scaletto.StarterApp
import libretto.stream.scaletto.DefaultStreams.ValSource

object Main extends StarterApp {
  import $.*
  import scalettoLib.printLine

  val nLargeBones = 20
  val nSmallBones = 2 * nLargeBones
  val nToys       = nLargeBones + nSmallBones
  val nBiscuits   = (nLargeBones * 3) + (nSmallBones * 5)

  val inToys     = List.fill(nToys)(Toy())
  val inBones    = List.fill(nLargeBones)(List(Bone.Small(), Bone.Large(), Bone.Small())).flatten
  val inBiscuits = List.fill(nBiscuits)(Biscuit())

  override def blueprint: Done -⚬ Done =
    λ.+ { trigger =>
      val toys     = trigger > ValSource.fromList(inToys)
      val bones    = trigger > ValSource.fromList(inBones)
      val biscuits = trigger > ValSource.fromList(inBiscuits)

      val treatsPacks: $[ValSource[TreatsPack]] =
        DogTreatsFactory.packagingLine(toys |*| bones |*| biscuits)

      treatsPacks > ValSource.forEachSequentially {
        printLine { pack => s"$pack" }
      }
    }
}
