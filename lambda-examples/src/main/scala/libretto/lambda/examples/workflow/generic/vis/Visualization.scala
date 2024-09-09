package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*

sealed trait Visualization {
  def breadth: Breadth
  def length: Length

  def aspectRatio: AspectRatio =
    AspectRatio(length, breadth)
}

object Visualization {
  case class Unimplemented(label: String) extends Visualization:
    override def length: Length = Length.one
    override def breadth: Breadth = Breadth.one

  case class Seq(a: Visualization, b: Visualization) extends Visualization:
    override def breadth: Breadth =
      Breadth.max(a.breadth, b.breadth)

    override def length: Length =
      Length.cram(a.length, b.length)

  case class Par(a: Visualization, b: Visualization) extends Visualization:
    override def breadth: Breadth =
      Breadth.cram(a.breadth, b.breadth)

    override def length: Length =
      Length.max(a.length, b.length)
}

