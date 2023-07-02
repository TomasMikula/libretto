package libretto.examples.tv

import libretto.scaletto.StarterKit.*
import libretto.stream.scaletto.DefaultStreams.*

object TvInterface {
  type Tv = Rec[TvF]

  type TvF[Tv] =
    ChannelsF[Tv] |&| TurnOff

  type TurnOff =
    Done

  type ChannelsF[Tv] =
    Val[TvChannel] =⚬ TvStreamF[Tv]

  type Channels = ChannelsF[Tv]

  type TvStreamF[Tv] =
    ValSourceT[Tv, VideoFrame]

  type TvStream = TvStreamF[Tv]

  object Tv {
    def createProvider[A](
      onWatch: A -⚬ Channels,
      onTurnOff: A -⚬ Done,
    ): A -⚬ Tv =
      choice(onWatch, onTurnOff) > pack[TvF]

    def watch: Tv -⚬ Channels =
      unpack > chooseL

    def turnOff: Tv -⚬ Done =
      unpack > chooseR
  }
}
