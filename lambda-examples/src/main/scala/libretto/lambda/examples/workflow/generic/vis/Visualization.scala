package libretto.lambda.examples.workflow.generic.vis

sealed trait Visualization {
  def heightToWidthRatio: Double
}

object Visualization {
  case class Unimplemented(label: String) extends Visualization:
    override def heightToWidthRatio: Double = 0.5
}

