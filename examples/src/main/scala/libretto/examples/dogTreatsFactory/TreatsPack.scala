package libretto.examples.dogTreatsFactory

import libretto.scaletto.StarterKit.{$, >, LambdaContext, Val, mapVal}

enum TreatsPack {
  case LargeBone(
    toy: Toy,
    bone: Bone.Large,
    biscuits: Biscuit3,
  )

  case SmallBone(
    toy: Toy,
    bone: Bone.Small,   // smaller bone,
    biscuits: Biscuit5, // but two more biscuits
  )

  override def toString: String =
    this match {
      case _: LargeBone => s"[1 toy, 1 large bone, 3 biscuits]"
      case _: SmallBone => s"[1 toy, 1 small bone, 5 biscuits]"
    }
}

object TreatsPack {
  def largeBone(toy: $[Val[Toy]], bone: $[Val[Bone.Large]], biscuits: $[Val[Biscuit3]])(using LambdaContext): $[Val[TreatsPack]] =
    (toy ** bone ** biscuits) > mapVal {
      case ((toy, bone), biscuits) => TreatsPack.LargeBone(toy, bone, biscuits)
    }

  def smallBone(toy: $[Val[Toy]], bone: $[Val[Bone.Small]], biscuits: $[Val[Biscuit5]])(using LambdaContext): $[Val[TreatsPack]] =
    (toy ** bone ** biscuits) > mapVal {
      case ((toy, bone), biscuits) => TreatsPack.SmallBone(toy, bone, biscuits)
    }
}

type Biscuit3 = (Biscuit, Biscuit, Biscuit)
type Biscuit5 = (Biscuit, Biscuit, Biscuit, Biscuit, Biscuit)

def Biscuit3(
  b1: $[Val[Biscuit]],
  b2: $[Val[Biscuit]],
  b3: $[Val[Biscuit]],
)(using
  LambdaContext,
): $[Val[Biscuit3]] =
  (b1 ** b2 ** b3) > mapVal { case ((b1, b2), b3) => (b1, b2, b3) }

def Biscuit5(
  b1: $[Val[Biscuit]],
  b2: $[Val[Biscuit]],
  b3: $[Val[Biscuit]],
  b4: $[Val[Biscuit]],
  b5: $[Val[Biscuit]],
)(using
  LambdaContext,
): $[Val[Biscuit5]] =
  (b1 ** b2 ** b3 ** b4 ** b5) > mapVal { case ((((b1, b2), b3), b4), b5) => (b1, b2, b3, b4, b5) }
