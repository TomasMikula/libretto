package libretto.examples.dogTreatsFactory

import libretto.scaletto.StarterKit.*
import libretto.stream.scaletto.DefaultStreams.ValSource

object DogTreatsFactory {

  def packagingLine: (ValSource[Toy] |*| ValSource[Bone] |*| ValSource[Biscuit]) -⚬ ValSource[TreatsPack] = {
    import ValSource.{Polled, close, poll}

    rec { self =>
      ValSource.from(
        onClose =
          λ { case (toys |*| bones |*| biscuits) =>
            joinAll(close(toys), close(bones), close(biscuits))
          },

        onPoll =
          λ { case (toys |*| bones |*| biscuits) =>
            poll(toys) either {
              case Left(done) =>
                // no toys left
                Polled.empty(joinAll(done, close(bones), close(biscuits)))

              case Right(toy |*| toys) =>
                // got a toy
                poll(bones) either {
                  case Left(done) =>
                    // no bones left
                    Polled.empty(joinAll(done, neglect(toy), close(toys), close(biscuits)))
                  case Right(bone |*| bones) =>
                    // got a bone
                    Bone.classifySize(bone) either {
                      case Left(largeBone) =>
                        // got a large bone
                        pullThreeBiscuits(biscuits) either {
                          case Left(done) =>
                            // not enough biscuits
                            Polled.empty(joinAll(done, neglect(toy), neglect(largeBone), close(toys), close(bones)))
                          case Right(biscuit3 |*| biscuits) =>
                            // got three biscuits
                            Polled.cons(
                              TreatsPack.largeBone(toy, largeBone, biscuit3) |*|
                              self(toys |*| bones |*| biscuits)
                            )
                        }
                      case Right(smallBone) =>
                        // got a small bone
                        pullFiveBiscuits(biscuits) either {
                            case Left(done) =>
                              // not enough biscuits
                              Polled.empty(joinAll(done, neglect(toy), neglect(smallBone), close(toys), close(bones)))
                            case Right(biscuit5 |*| biscuits) =>
                              // got five biscuits
                              Polled.cons(
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
  }

  private def pullThreeBiscuits: ValSource[Biscuit] -⚬ (Done |+| (Val[Biscuit3] |*| ValSource[Biscuit])) = {
    import ValSource.poll

    λ { biscuits =>
      poll(biscuits) either {
        case Left(done) =>
          injectL(done)
        case Right(b1 |*| biscuits) =>
          poll(biscuits) either {
            case Left(done) =>
              joinAll(done, neglect(b1)) > injectL
            case Right(b2 |*| biscuits) =>
              poll(biscuits) either {
                case Left(done) =>
                  joinAll(done, neglect(b1), neglect(b2)) > injectL
                case Right(b3 |*| biscuits) =>
                  (Biscuit3(b1, b2, b3) |*| biscuits) > injectR
              }
          }
      }
    }
  }

  private def pullFiveBiscuits: ValSource[Biscuit] -⚬ (Done |+| (Val[Biscuit5] |*| ValSource[Biscuit])) = {
    import ValSource.poll

    λ { biscuits =>
      pullThreeBiscuits(biscuits) either {
        case Left(done) =>
          injectL(done)
        case Right(biscuit3 |*| biscuits) =>
          poll(biscuits) either {
            case Left(done) =>
              joinAll(done, neglect(biscuit3)) > injectL
            case Right(b4 |*| biscuits) =>
              poll(biscuits) either {
                case Left(done) =>
                  joinAll(done, neglect(biscuit3), neglect(b4)) > injectL
                case Right(b5 |*| biscuits) =>
                  val biscuit5 = (biscuit3 ** b4 ** b5) > mapVal { case (((b1, b2, b3), b4), b5) => (b1, b2, b3, b4, b5) }
                  injectR(biscuit5 |*| biscuits)
              }
          }
      }
    }
  }

}
