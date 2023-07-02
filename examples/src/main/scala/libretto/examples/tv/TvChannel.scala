package libretto.examples.tv

object TvChannel {
  case class Discovery()
  case class Cooking()
  case class Sport()
}

import TvChannel.*

type TvChannel = Discovery | Cooking | Sport