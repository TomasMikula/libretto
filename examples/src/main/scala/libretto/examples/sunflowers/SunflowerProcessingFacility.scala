package libretto.examples.sunflowers

import libretto.scaletto.StarterKit.*
import libretto.stream.scaletto.DefaultStreams.ValSource
import libretto.stream.scaletto.DefaultStreams.ValSource.{Polled, fromChoice, notifyAction, poll}

object SunflowerProcessingFacility {
  def blueprint: ValSource[Sunflower] -⚬ (ValSource[SeedsPack] |*| ValSource[OilBottle]) = rec { self =>
    λ { sunflowers =>
      // give names to the outputs
      producing { case seedsOut |*| oilOut =>
        // race the outputs by which one acts (i.e. pulls or closes) first
        (selectBy(notifyAction, notifyAction) >>: (seedsOut |*| oilOut)) choose {
          // seed output acted first
          case Left (seedsOut |*| oilOut) =>
            (fromChoice >>: seedsOut) choose {
              case Left(closingSeeds) =>
                returning(
                  oilOut       := sunflowers :>> oilOnlyMode,
                  closingSeeds := constant(done),
                )
              case Right(pullingSeeds) =>
                (pullingSeeds |*| oilOut) :=
                  switch ( pull3(sunflowers) )
                    .is { case InR(sunflower3 |*| sunflowers) =>
                      // got 3 sunflowers, let's roast the seeds and package them
                      val seedsPack = roastSeedsAndPack(sunflower3)
                      // operate recursively on the rest of the input source
                      val seedsPacks |*| oilBottles = self(sunflowers)
                      Polled.cons(seedsPack |*| seedsPacks) |*| oilBottles
                    }
                    .is { case InL(+(closed)) =>
                      // no more sunflowers
                      Polled.empty(closed) |*| ValSource.empty(closed)
                    }
                    .end
            }
          // oil output acted first
          case Right(seedsOut |*| oilOut) =>
            (fromChoice >>: oilOut) choose {
              case Left(closingOil) =>
                returning(
                  seedsOut   := sunflowers :>> seedsOnlyMode,
                  closingOil := constant(done),
                )
              case Right(pullingOil) =>
                (seedsOut |*| pullingOil) :=
                  switch ( pull5(sunflowers) )
                    .is { case InR(sunflower5 |*| sunflowers) =>
                      val oilBottle = makeOil(sunflower5)
                      val seedsPacks |*| oilBottles = self(sunflowers)
                      seedsPacks |*| Polled.cons(oilBottle |*| oilBottles)
                    }
                    .is { case InL(+(closed)) =>
                      ValSource.empty(closed) |*| Polled.empty(closed)
                    }
                    .end
            }
        }
      }
    }
  }

  private def oilOnlyMode: ValSource[Sunflower] -⚬ ValSource[OilBottle] = rec { self =>
    λ { sunflowers =>
      producing { oilOut =>
        (fromChoice >>: oilOut) choose {
          case Left(closing) =>
            closing := ValSource.close(sunflowers)
          case Right(pulling) =>
            pulling := switch ( pull5(sunflowers) )
              .is { case InL(closed)      => Polled.empty(closed) }
              .is { case InR(sf5 |*| sfs) => Polled.cons(makeOil(sf5) |*| self(sfs)) }
              .end
        }
      }
    }
  }

  private def seedsOnlyMode: ValSource[Sunflower] -⚬ ValSource[SeedsPack] = rec { self =>
    λ { sunflowers =>
      producing { seedsOut =>
        (fromChoice >>: seedsOut) choose {
          case Left(closing) =>
            closing := ValSource.close(sunflowers)
          case Right(pulling) =>
            pulling := switch ( pull3(sunflowers) )
              .is { case InL(closed)      => Polled.empty(closed) }
              .is { case InR(sf3 |*| sfs) => Polled.cons(roastSeedsAndPack(sf3) |*| self(sfs)) }
              .end
        }
      }
    }
  }

  private type Sunflower3 = (Sunflower, Sunflower, Sunflower)
  private type Sunflower5 = (Sunflower, Sunflower, Sunflower, Sunflower, Sunflower)

  private def pull3: ValSource[Sunflower] -⚬ (Done |+| (Val[Sunflower3] |*| ValSource[Sunflower])) =
    λ { src =>
      switch ( poll(src) )
        .is { case InL(closed) => InL(closed) }
        .is { case InR(sf1 |*| tail) =>
          switch ( poll(tail) )
            .is { case InL(closed) => InL(joinAll(neglect(sf1), closed)) }
            .is { case InR(sf2 |*| tail) =>
              switch ( poll(tail) )
                .is { case InL(closed) => InL(joinAll(neglect(sf1), neglect(sf2), closed)) }
                .is { case InR(sf3 |*| tail) => InR(tuple(sf1, sf2, sf3) |*| tail) }
                .end
            }.end
        }.end
    }

  private def pull5: ValSource[Sunflower] -⚬ (Done |+| (Val[Sunflower5] |*| ValSource[Sunflower])) =
    λ { src =>
      switch ( pull3(src) )
        .is { case InL(closed) => InL(closed) }
        .is { case InR(sf3 |*| tail) =>
          switch( poll(tail) )
            .is { case InL(closed) => InL(joinAll(neglect(sf3), closed)) }
            .is { case InR(sf4 |*| tail) =>
              switch( poll(tail) )
                .is { case InL(closed) => InL(joinAll(neglect(sf3), neglect(sf4), closed)) }
                .is { case InR(sf5 |*| tail) =>
                  val res = tuple(sf3, sf4, sf5) > mapVal { case ((s1, s2, s3), s4, s5) => (s1, s2, s3, s4, s5) }
                  InR(res |*| tail)
                }.end
            }.end
        }.end
    }

  private def roastSeedsAndPack: Val[Sunflower3] -⚬ Val[SeedsPack] =
    mapVal(_ => SeedsPack())

  private def makeOil: Val[Sunflower5] -⚬ Val[OilBottle] =
    mapVal(_ => OilBottle())
}
