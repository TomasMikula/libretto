package libretto.lambda.examples.workflow.generic.vis

sealed trait WirePick[X] {

}

object WirePick {
  case class Fst[B]() extends WirePick[(Wire, B)]
  case class Snd[A]() extends WirePick[(A, Wire)]

  def fst[B]: WirePick[(Wire, B)] = Fst()
  def snd[A]: WirePick[(A, Wire)] = Snd()
}
