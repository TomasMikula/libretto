package libretto.examples.tv

import libretto.scaletto.StarterKit.*
import libretto.scaletto.StarterKit.$.*
import libretto.stream.scaletto.DefaultStreams.*
import TvChannel.{Cooking, Discovery, Sport}
import TvInterface.*
import TvInterface.Tv.{turnOff, watch}

object TvViewer {
  def blueprint: Tv -⚬ Done =
    λ { tv =>
      val video = watch(tv)(constant(done > pickChannel(Discovery())))
      consume(60)(video) match
        case done |*| tv =>
          val video = watch(tv)(done :>> pickChannel(Cooking()))
          consume(30)(video) match
            case done |*| tv =>
              val video = watch(tv)(done :>> pickChannel(Sport()))
              consume(15)(video) match
                case done |*| tv =>
                  joinAll(
                    done :>> printLine(s"Done with TV."),
                    turnOff(tv),
                  )
    }

  private def pickChannel(ch: TvChannel): Done -⚬ Val[TvChannel] =
    printLine(s"Switching to channel $ch") > constVal(ch)

  private def consume(length: Int): TvStream -⚬ (Done |*| Tv) =
    ValSourceT.take(length) > λ { case n0 |*| src =>
      val (done |*| tv) = src :>> ValSourceT.forEachSequentially(consumeFrame)
      join(neglect(n0) |*| done) |*| tv
    }

  private def consumeFrame: Val[VideoFrame] -⚬ Done =
    mapVal[VideoFrame, String](_.value) > printLine
}
