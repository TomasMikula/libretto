package libretto.examples.dogTreatsFactory

import libretto.scaletto.StarterKit.{$, -⚬, |*|, |+|, Done, Val, injectL, injectR, mapVal, neglect, rec, λ}
import libretto.scaletto.StarterKit.$._
import libretto.scaletto.StarterKit.coreLib.|+|.{switch, switchWith}
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
          poll(toys)
            .switchWith(bones |*| biscuits)(
              caseLeft =
                // no toys left
                λ { case (done |*| (bones |*| biscuits)) =>
                  injectL(joinAll(done, close(bones), close(biscuits)))
                },

              caseRight =
                λ { case ((toy |*| toys) |*| (bones |*| biscuits)) =>
                  // got a toy
                  poll(bones)
                    .switchWith(toy |*| toys |*| biscuits)(
                      caseLeft =
                        // no bones left
                        λ { case (done |*| (toy |*| toys |*| biscuits)) =>
                          injectL(joinAll(done, neglect(toy), close(toys), close(biscuits)))
                        },
                      caseRight =
                        // got a bone
                        λ { case ((bone |*| bones) |*| (toy |*| toys |*| biscuits)) =>
                          Bone.classifySize(bone)
                            .switchWith(toy |*| toys |*| bones |*| biscuits)(
                              caseLeft =
                                // got a large bone
                                λ { case (largeBone |*| (toy |*| toys |*| bones |*| biscuits)) =>
                                  pullThreeBiscuits(biscuits)
                                    .switchWith(toy |*| largeBone |*| toys |*| bones)(
                                      caseLeft =
                                        // not enough biscuits
                                        λ { case (done |*| (toy |*| largeBone |*| toys |*| bones)) =>
                                          injectL(joinAll(done, neglect(toy), neglect(largeBone), close(toys), close(bones)))
                                        },
                                      caseRight =
                                        // got three biscuits
                                        λ { case ((biscuit3 |*| biscuits) |*| (toy |*| largeBone |*| toys |*| bones)) =>
                                          injectR(
                                            TreatsPack.largeBone(toy, largeBone, biscuit3) |*|
                                            self(toys |*| bones |*| biscuits)
                                          )
                                        }
                                    )
                                },
                              caseRight =
                                // got a small bone
                                λ { case (smallBone |*| (toy |*| toys |*| bones |*| biscuits)) =>
                                  pullFiveBiscuits(biscuits)
                                    .switchWith(toy |*| smallBone |*| toys |*| bones)(
                                      caseLeft =
                                        // not enough biscuits
                                        λ { case (done |*| (toy |*| smallBone |*| toys |*| bones)) =>
                                          injectL(joinAll(done, neglect(toy), neglect(smallBone), close(toys), close(bones)))
                                        },
                                      caseRight =
                                        // got five biscuits
                                        λ { case ((biscuit5 |*| biscuits) |*| (toy |*| smallBone |*| toys |*| bones)) =>
                                          injectR(
                                            TreatsPack.smallBone(toy, smallBone, biscuit5) |*|
                                            self(toys |*| bones |*| biscuits)
                                          )
                                        }
                                    )
                                }
                            )
                        }
                    )
                }
            )
        },
    )
  }

  private def pullThreeBiscuits: Pollable[Biscuit] -⚬ (Done |+| (Val[Biscuit3] |*| Pollable[Biscuit])) = {
    import Pollable.poll

    λ { biscuits =>
      poll(biscuits).switch(
        caseLeft =
          λ { done => injectL(done) },
        caseRight =
          λ { case (b1 |*| biscuits) =>
            poll(biscuits).switchWith(b1)(
              caseLeft =
                λ { case (done |*| b1) => joinAll(done, neglect(b1)) > injectL },
              caseRight =
                λ { case ((b2 |*| biscuits) |*| b1) =>
                  poll(biscuits).switchWith(b1 |*| b2)(
                    caseLeft =
                      λ { case (done |*| (b1 |*| b2)) => joinAll(done, neglect(b1), neglect(b2)) > injectL },
                    caseRight =
                      λ { case ((b3 |*| biscuits) |*| (b1 |*| b2)) => (Biscuit3(b1, b2, b3) |*| biscuits) > injectR },
                  )
                },
            )
          },
      )
    }
  }

  private def pullFiveBiscuits: Pollable[Biscuit] -⚬ (Done |+| (Val[Biscuit5] |*| Pollable[Biscuit])) = {
    import Pollable.poll

    λ { biscuits =>
      pullThreeBiscuits(biscuits).switch(
        caseLeft =
          λ { done => injectL(done) },
        caseRight =
          λ { case (biscuit3 |*| biscuits) =>
            poll(biscuits).switchWith(biscuit3)(
              caseLeft =
                λ { case (done |*| biscuit3) => joinAll(done, neglect(biscuit3)) > injectL },
              caseRight =
                λ { case ((b4 |*| biscuits) |*| biscuit3) =>
                  poll(biscuits).switchWith(biscuit3 |*| b4)(
                    caseLeft =
                      λ { case (done |*| (biscuit3 |*| b4)) => joinAll(done, neglect(biscuit3), neglect(b4)) > injectL },
                    caseRight =
                      λ { case ((b5 |*| biscuits) |*| (biscuit3 |*| b4)) =>
                        val biscuit5 = (biscuit3 * b4 * b5) > mapVal { case (((b1, b2, b3), b4), b5) => (b1, b2, b3, b4, b5) }
                        injectR(biscuit5 |*| biscuits)
                      },
                  )
                }
            )
          },
      )
    }
  }

}
