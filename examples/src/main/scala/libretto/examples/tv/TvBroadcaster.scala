package libretto.examples.tv

import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.$._
import libretto.stream.scaletto.DefaultStreams._
import TvChannel.{Cooking, Discovery, Sport}
import TvInterface.{Channels, Tv, TvStream}

object TvBroadcaster {
  def blueprint: Done -⚬ Tv = rec { self =>
    Tv.createProvider(on(self), off)
  }

  private def off: Done -⚬ Done =
    id[Done]

  private def on(makeTv: Done -⚬ Tv): Done -⚬ Channels = {
    def go(ch: TvChannel): Done -⚬ TvStream =
      λ.+ { d =>
        val vidSrc = d :>> videoSource(ch)
        val repeat = one :>> Detained.thunk(makeTv)
        ValSource.terminateWith(vidSrc |*| repeat)
      }

    λ { start =>
      λ.closure { ch =>
        switch(ch)
          .Case[Discovery] { ch => join(start |*| neglect(ch)) :>> go(Discovery()) }
          .Case[Cooking]   { ch => join(start |*| neglect(ch)) :>> go(Cooking())   }
          .Case[Sport]     { ch => join(start |*| neglect(ch)) :>> go(Sport())     }
          .endswitch
      }
    }
  }

  private def videoSource(ch: TvChannel): Done -⚬ ValSource[VideoFrame] =
    ValSource.fromList(
      ch match {
        case Discovery() => Content.Discovery
        case Cooking()   => Content.Cooking
        case Sport()     => Content.Sport
      }
    ) > ValSource.map(VideoFrame(_))

  private object Content {
    val Discovery =
      List(
        "🐵", "🐒", "🦍", "🦧", "🐶", "🐕", "🦮", "🐕‍🦺", "🐩", "🐺",
        "🦊", "🦝", "🐱", "🐈", "🐈‍⬛", "🦁", "🐯", "🐅", "🐆", "🐴",
        "🐎", "🦄", "🦓", "🦌", "🦬", "🐮", "🐄", "🐂", "🐃", "🐷",
        "🐖", "🐗", "🐽", "🐏", "🐑", "🐐", "🐪", "🐫", "🦙", "🦒",
        "🐘", "🦣", "🦏", "🦛", "🐭", "🐁", "🐀", "🐹", "🐰", "🐇",
        "🐿", "🦫", "🦔", "🦇", "🐻", "🐻‍❄️", "🐨", "🐼", "🦥", "🦦",
        "🦨", "🦘", "🦡", "🐾", "🦃", "🐔", "🐓", "🐣", "🐤", "🐥",
        "🐦", "🐦‍⬛", "🐧", "🕊", "🦅", "🦆", "🦢", "🦉", "🦤", "🪶",
        "🦩", "🦜", "🐸", "🐊", "🐢", "🦎", "🐍", "🐲", "🐉", "🦕",
        "🦖", "🐳", "🐋", "🐬", "🦭", "🐟", "🐠", "🐡", "🦈", "🐙",
        "🐚", "🐌", "🦋", "🐛", "🐜", "🐝", "🪲", "🐞", "🦗", "🪳",
        "🕷", "🕸", "🦂", "🦟", "🪰", "🪱", "🦠", "💐", "🌸", "💮",
        "🏵", "🌹", "🥀", "🌺", "🌻", "🌼", "🌷", "🌱", "🪴", "🌲",
        "🌳", "🌴", "🌵", "🌾", "🌿", "☘", "🍀", "🍁", "🍂", "🍃",
      )

    val Cooking =
      List(
        "🍇", "🍈", "🍉", "🍊", "🍋", "🍌", "🍍", "🥭", "🍎", "🍏",
        "🍐", "🍑", "🍒", "🍓", "🫐", "🥝", "🍅", "🫒", "🥥", "🥑",
        "🍆", "🥔", "🥕", "🌽", "🌶", "🫑", "🥒", "🥬", "🥦", "🧄",
        "🧅", "🍄", "🥜", "🫑", "🌰", "🍞", "🥐", "🥖", "🫓", "🥨",
        "🥯", "🥞", "🧇", "🧀", "🍖", "🍗", "🥩", "🥓", "🍔", "🍟",
        "🍕", "🌭", "🥪", "🌮", "🌯", "🫔", "🥙", "🧆", "🥚", "🍳",
        "🥘", "🍲", "🫕", "🥣", "🥗", "🍿", "🧈", "🧂", "🥫", "🍱",
        "🍘", "🍙", "🍚", "🍛", "🍜", "🍝", "🍠", "🍢", "🍣", "🍤",
        "🍥", "🥮", "🍡", "🥟", "🥠", "🥡", "🦀", "🦞", "🦐", "🦑",
        "🦪", "🍨", "🍧", "🍦", "🍩", "🍪", "🎂", "🍰", "🧁", "🥧",
        "🍫", "🍬", "🍭", "🍮", "🍯", "🍼", "🥛", "☕", "🫖", "🍵",
        "🍶", "🍾", "🍷", "🍸", "🍹", "🍺", "🍻", "🥂", "🥃", "🥤",
        "🧋", "🧃", "🧉", "🧊", "🥢", "🍽", "🍴", "🥄", "🔪", "🧋",
        "🏺",
      )

    val Sport =
      List(
        "⚽", "⚾", "🥎", "🏀", "🏐", "🏈", "🏉", "🎾", "🥏", "🎳",
        "🏏", "🏑", "🏒", "🥍", "🏓", "🏸", "🥊", "🥋", "🥅", "⛳",
        "⛸", "🎣", "🤿", "🎽", "🎿", "🛷", "🥌",
      )
  }
}
