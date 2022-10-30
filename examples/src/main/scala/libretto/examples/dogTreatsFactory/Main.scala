package libretto.examples.dogTreatsFactory

import libretto.scaletto.StarterApp

object Main extends StarterApp {
  import $._
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
      val toys     = trigger > Pollable.fromList(inToys)
      val bones    = trigger > Pollable.fromList(inBones)
      val biscuits = trigger > Pollable.fromList(inBiscuits)

      val treatsPacks: $[Pollable[TreatsPack]] =
        DogTreatsFactory.blueprint(toys |*| bones |*| biscuits)

      treatsPacks > Pollable.forEachSequentially {
        printLine { pack => s"$pack" }
      }
    }
}
