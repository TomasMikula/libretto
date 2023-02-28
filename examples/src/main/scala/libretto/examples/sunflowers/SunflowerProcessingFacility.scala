package libretto.examples.sunflowers

import libretto.scaletto.StarterKit._
import libretto.stream.scaletto.DefaultStreams.ValSource
import libretto.stream.scaletto.DefaultStreams.ValSource.{Polled, fromChoice, notifyAction, poll}

object SunflowerProcessingFacility {
  def blueprint: ValSource[Sunflower] -⚬ (ValSource[SeedsPack] |*| ValSource[OilBottle]) = rec { self =>
    λ { sunflowers =>
      // give names to the outputs
      producing { case seedsOut |*| oilOut =>
        // race the outputs by which one acts (i.e. pulls or closes) first
        (selectBy(notifyAction, notifyAction) >>: (seedsOut |*| oilOut)) switch {
          // seed output acted first
          case Left (seedsOut |*| oilOut) =>
            (fromChoice >>: seedsOut) switch {
              case Left(closingSeeds) =>
                returning(
                  oilOut       := sunflowers :>> oilOnlyMode,
                  closingSeeds := constant(done),
                )
              case Right(pullingSeeds) =>
                (pullingSeeds |*| oilOut) :=
                  pull3(sunflowers) switch {
                    case Right(sunflower3 |*| sunflowers) =>
                      // got 3 sunflowers, let's roast the seeds and package them
                      val seedsPack = roastSeedsAndPack(sunflower3)
                      // operate recursively on the rest of the input source
                      val seedsPacks |*| oilBottles = self(sunflowers)
                      Polled.cons(seedsPack |*| seedsPacks) |*| oilBottles
                    case Left(+(closed)) =>
                      // no more sunflowers
                      Polled.empty(closed) |*| ValSource.empty(closed)
                  }
            }
          // oil output acted first
          case Right(seedsOut |*| oilOut) =>
            (fromChoice >>: oilOut) switch {
              case Left(closingOil) =>
                returning(
                  seedsOut   := sunflowers :>> seedsOnlyMode,
                  closingOil := constant(done),
                )
              case Right(pullingOil) =>
                (seedsOut |*| pullingOil) :=
                  pull5(sunflowers) switch {
                    case Right(sunflower5 |*| sunflowers) =>
                      val oilBottle = makeOil(sunflower5)
                      val seedsPacks |*| oilBottles = self(sunflowers)
                      seedsPacks |*| Polled.cons(oilBottle |*| oilBottles)
                    case Left(+(closed)) =>
                      ValSource.empty(closed) |*| Polled.empty(closed)
                  }
            }
        }
      }
    }
  }

  private def oilOnlyMode: ValSource[Sunflower] -⚬ ValSource[OilBottle] = rec { self =>
    λ { sunflowers =>
      producing { oilOut =>
        (fromChoice >>: oilOut) switch {
          case Left(closing) =>
            closing := ValSource.close(sunflowers)
          case Right(pulling) =>
            pulling := pull5(sunflowers) switch {
              case Left(closed)       => Polled.empty(closed)
              case Right(sf5 |*| sfs) => Polled.cons(makeOil(sf5) |*| self(sfs))
            }
        }
      }
    }
  }

  private def seedsOnlyMode: ValSource[Sunflower] -⚬ ValSource[SeedsPack] = rec { self =>
    λ { sunflowers =>
      producing { seedsOut =>
        (fromChoice >>: seedsOut) switch {
          case Left(closing) =>
            closing := ValSource.close(sunflowers)
          case Right(pulling) =>
            pulling := pull3(sunflowers) switch {
              case Left(closed)       => Polled.empty(closed)
              case Right(sf3 |*| sfs) => Polled.cons(roastSeedsAndPack(sf3) |*| self(sfs))
            }
        }
      }
    }
  }

  private type Sunflower3 = (Sunflower, Sunflower, Sunflower)
  private type Sunflower5 = (Sunflower, Sunflower, Sunflower, Sunflower, Sunflower)

  private def pull3: ValSource[Sunflower] -⚬ (Done |+| (Val[Sunflower3] |*| ValSource[Sunflower])) =
    λ { src =>
      poll(src) switch {
        case Left(closed) =>
          injectL(closed)
        case Right(sf1 |*| tail) =>
          poll(tail) switch {
            case Left(closed) =>
              injectL(joinAll(neglect(sf1), closed))
            case Right(sf2 |*| tail) =>
              poll(tail) switch {
                case Left(closed) =>
                  injectL(joinAll(neglect(sf1), neglect(sf2), closed))
                case Right(sf3 |*| tail) =>
                  injectR(tuple(sf1, sf2, sf3) |*| tail)
              }
          }
      }
    }

  private def pull5: ValSource[Sunflower] -⚬ (Done |+| (Val[Sunflower5] |*| ValSource[Sunflower])) =
    λ { src =>
      pull3(src) switch {
        case Left(closed) =>
          injectL(closed)
        case Right(sf3 |*| tail) =>
          poll(tail) switch {
            case Left(closed) =>
              injectL(joinAll(neglect(sf3), closed))
            case Right(sf4 |*| tail) =>
              poll(tail) switch {
                case Left(closed) =>
                  injectL(joinAll(neglect(sf3), neglect(sf4), closed))
                case Right(sf5 |*| tail) =>
                  val res = tuple(sf3, sf4, sf5) > mapVal { case ((s1, s2, s3), s4, s5) => (s1, s2, s3, s4, s5) }
                  injectR(res |*| tail)
              }
          }
      }
    }

  private def roastSeedsAndPack: Val[Sunflower3] -⚬ Val[SeedsPack] =
    mapVal(_ => SeedsPack())

  private def makeOil: Val[Sunflower5] -⚬ Val[OilBottle] =
    mapVal(_ => OilBottle())
}
