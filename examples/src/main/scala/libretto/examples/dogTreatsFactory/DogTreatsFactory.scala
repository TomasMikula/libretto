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
            switch ( poll(toys) )
              .is { case InL(done) =>
                // no toys left
                Polled.empty(joinAll(done, close(bones), close(biscuits)))
              }
              .is { case InR(toy |*| toys) =>
                // got a toy
                switch ( poll(bones) )
                  .is { case InL(done) =>
                    // no bones left
                    Polled.empty(joinAll(done, neglect(toy), close(toys), close(biscuits)))
                  }
                  .is { case InR(bone |*| bones) =>
                    // got a bone
                    switch ( Bone.classifySize(bone) )
                      .is { case InL(largeBone) =>
                        // got a large bone
                        switch ( pullThreeBiscuits(biscuits) )
                          .is { case InL(done) =>
                            // not enough biscuits
                            Polled.empty(joinAll(done, neglect(toy), neglect(largeBone), close(toys), close(bones)))
                          }
                          .is { case InR(biscuit3 |*| biscuits) =>
                            // got three biscuits
                            Polled.cons(
                              TreatsPack.largeBone(toy, largeBone, biscuit3) |*|
                              self(toys |*| bones |*| biscuits)
                            )
                          }.end
                      }
                      .is { case InR(smallBone) =>
                        // got a small bone
                        switch ( pullFiveBiscuits(biscuits) )
                          .is { case InL(done) =>
                            // not enough biscuits
                            Polled.empty(joinAll(done, neglect(toy), neglect(smallBone), close(toys), close(bones)))
                          }
                          .is { case InR(biscuit5 |*| biscuits) =>
                            // got five biscuits
                            Polled.cons(
                              TreatsPack.smallBone(toy, smallBone, biscuit5) |*|
                              self(toys |*| bones |*| biscuits)
                            )
                          }.end
                      }.end
                  }.end
              }.end
          },
      )
    }
  }

  private def pullThreeBiscuits: ValSource[Biscuit] -⚬ (Done |+| (Val[Biscuit3] |*| ValSource[Biscuit])) = {
    import ValSource.poll

    λ { biscuits =>
      switch ( poll(biscuits) )
        .is { case InL(done) => InL(done) }
        .is { case InR(b1 |*| biscuits) =>
          switch ( poll(biscuits) )
            .is { case InL(done) => InL(joinAll(done, neglect(b1))) }
            .is { case InR(b2 |*| biscuits) =>
              switch ( poll(biscuits) )
                .is { case InL(done) => InL(joinAll(done, neglect(b1), neglect(b2))) }
                .is { case InR(b3 |*| biscuits) => InR(Biscuit3(b1, b2, b3) |*| biscuits) }
                .end
            }.end
        }.end
    }
  }

  private def pullFiveBiscuits: ValSource[Biscuit] -⚬ (Done |+| (Val[Biscuit5] |*| ValSource[Biscuit])) = {
    import ValSource.poll

    λ { biscuits =>
      switch ( pullThreeBiscuits(biscuits) )
        .is { case InL(done) => InL(done) }
        .is { case InR(biscuit3 |*| biscuits) =>
          switch ( poll(biscuits) )
            .is { case InL(done) => InL(joinAll(done, neglect(biscuit3))) }
            .is { case InR(b4 |*| biscuits) =>
              switch ( poll(biscuits) )
                .is { case InL(done) =>
                  InL(joinAll(done, neglect(biscuit3), neglect(b4)))
                }
                .is { case InR(b5 |*| biscuits) =>
                  val biscuit5 = (biscuit3 ** b4 ** b5) |> mapVal { case (((b1, b2, b3), b4), b5) => (b1, b2, b3, b4, b5) }
                  InR(biscuit5 |*| biscuits)
                }.end
            }.end
        }.end
    }
  }

}
