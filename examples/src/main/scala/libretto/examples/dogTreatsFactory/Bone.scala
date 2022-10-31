package libretto.examples.dogTreatsFactory

import libretto.scaletto.StarterKit.{-⚬, |+|, Val, id, liftEither, mapVal}

enum Bone {
  case Large()
  case Small()
}

object Bone {
  val classifySize: Val[Bone] -⚬ (Val[Bone.Large] |+| Val[Bone.Small]) =
    id[Val[Bone]] >
    mapVal {
      case b: Bone.Large => Left(b)
      case b: Bone.Small => Right(b)
    } >
    liftEither
}
