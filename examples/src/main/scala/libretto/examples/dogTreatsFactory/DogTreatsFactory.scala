package libretto.examples.dogTreatsFactory

import libretto.scaletto.StarterKit.{$, -⚬, |*|, |+|, Done, Val, injectL, injectR, mapVal, neglect, rec, λ}
import libretto.scaletto.StarterKit.$._
import libretto.scaletto.StarterKit.scalettoStreams.Pollable

object DogTreatsFactory {

  def blueprint: (Pollable[Toy] |*| Pollable[Bone] |*| Pollable[Biscuit]) -⚬ Pollable[TreatsPack] = rec { self =>
    import Pollable.{close, poll}

    Pollable.from(
      onClose =
        λ { case (toys |*| bones |*| biscuits) =>
          joinAll(close(toys), close(bones), close(biscuits))
        },

      onPoll =
        λ { case (toys |*| bones |*| biscuits) =>
          poll(toys) switch {
            case Left(done) =>
              // no toys left
              injectL(joinAll(done, close(bones), close(biscuits)))

            case Right(toy |*| toys) =>
              // got a toy
              poll(bones) switch {
                case Left(done) =>
                  // no bones left
                  injectL(joinAll(done, neglect(toy), close(toys), close(biscuits)))
                case Right(bone |*| bones) =>
                  // got a bone
                  Bone.classifySize(bone) switch {
                    case Left(largeBone) =>
                      // got a large bone
                      pullThreeBiscuits(biscuits) switch {
                        case Left(done) =>
                          // not enough biscuits
                          injectL(joinAll(done, neglect(toy), neglect(largeBone), close(toys), close(bones)))
                        case Right(biscuit3 |*| biscuits) =>
                          // got three biscuits
                          injectR(
                            TreatsPack.largeBone(toy, largeBone, biscuit3) |*|
                            self(toys |*| bones |*| biscuits)
                          )
                      }
                    case Right(smallBone) =>
                      // got a small bone
                      pullFiveBiscuits(biscuits) switch {
                          case Left(done) =>
                            // not enough biscuits
                            injectL(joinAll(done, neglect(toy), neglect(smallBone), close(toys), close(bones)))
                          case Right(biscuit5 |*| biscuits) =>
                            // got five biscuits
                            injectR(
                              TreatsPack.smallBone(toy, smallBone, biscuit5) |*|
                              self(toys |*| bones |*| biscuits)
                            )
                      }
                  }
              }
          }
        },
    )
  }

  private def pullThreeBiscuits: Pollable[Biscuit] -⚬ (Done |+| (Val[Biscuit3] |*| Pollable[Biscuit])) = {
    import Pollable.poll

    λ { biscuits =>
      poll(biscuits) switch {
        case Left(done) =>
          injectL(done)
        case Right(b1 |*| biscuits) =>
          poll(biscuits) switch {
            case Left(done) =>
              joinAll(done, neglect(b1)) > injectL
            case Right(b2 |*| biscuits) =>
              poll(biscuits) switch {
                case Left(done) =>
                  joinAll(done, neglect(b1), neglect(b2)) > injectL
                case Right(b3 |*| biscuits) =>
                  (Biscuit3(b1, b2, b3) |*| biscuits) > injectR
              }
          }
      }
    }
  }

  private def pullFiveBiscuits: Pollable[Biscuit] -⚬ (Done |+| (Val[Biscuit5] |*| Pollable[Biscuit])) = {
    import Pollable.poll

    λ { biscuits =>
      pullThreeBiscuits(biscuits) switch {
        case Left(done) =>
          injectL(done)
        case Right(biscuit3 |*| biscuits) =>
          poll(biscuits) switch {
            case Left(done) =>
              joinAll(done, neglect(biscuit3)) > injectL
            case Right(b4 |*| biscuits) =>
              poll(biscuits) switch {
                case Left(done) =>
                  joinAll(done, neglect(biscuit3), neglect(b4)) > injectL
                case Right(b5 |*| biscuits) =>
                  val biscuit5 = (biscuit3 * b4 * b5) > mapVal { case (((b1, b2, b3), b4), b5) => (b1, b2, b3, b4, b5) }
                  injectR(biscuit5 |*| biscuits)
              }
          }
      }
    }
  }

}
