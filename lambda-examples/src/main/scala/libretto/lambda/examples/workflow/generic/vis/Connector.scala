package libretto.lambda.examples.workflow.generic.vis

sealed trait Connector[X, Y] {

}

object Connector {
  case class Across[X, Y](
    src: WirePick[X],
    tgt: WirePick[Y],
  ) extends Connector[X, Y]
}
