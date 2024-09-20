package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*

sealed trait Visualization[X, Y] {
  def ioProportions: IOProportions[X, Y]
  def length: Length

  def breadth: Breadth =
    ioProportions.totalBreadth

  def aspectRatio: AspectRatio =
    AspectRatio(length, breadth)
}

object Visualization {
  case class Unimplemented[X, Y](label: String) extends Visualization[X, Y]:
    require(label.nonEmpty, "Label must not be empty string")

    override def length: Length = Length.one
    override def ioProportions: IOProportions[X, Y] = IOProportions.Unimplemented(Breadth.one)

  case class Seq[X, Y1, Y2, Z](
    a: Visualization[X, Y1],
    m: Morph[Y1, Y2],
    b: Visualization[Y2, Z],
  ) extends Visualization[X, Z]:
    override def ioProportions: IOProportions[X, Z] =
      IOProportions.Unimplemented(
        Breadth.max(a.breadth, b.breadth)
      )

    override def length: Length =
      Length.cram(a.length, b.length)

  case class Par[∙[_, _], X1, X2, Y1, Y2](
    a: Visualization[X1, Y1],
    b: Visualization[X2, Y2],
  ) extends Visualization[X1 ∙ X2, Y1 ∙ Y2]:
    override def ioProportions: IOProportions[X1 ∙ X2, Y1 ∙ Y2] =
      IOProportions.Unimplemented(
        Breadth.cram(a.breadth, b.breadth)
      )

    override def length: Length =
      Length.max(a.length, b.length)

  case class Merge[∙[_, _], X]() extends Visualization[X ∙ X, X]:
    override def ioProportions: IOProportions[X ∙ X, X] =
      IOProportions.Unimplemented(
        // XXX: should take preferred breadth as constructor parameter
        Breadth.cram(Breadth.one, Breadth.one)
      )

    override def length: Length =
      Length.cram(Length.one, Length.one)

  def par[∙[_, _]]: ParBuilder[∙] =
    ParBuilder[∙]

  class ParBuilder[∙[_, _]]:
    def apply[X1, X2, Y1, Y2](
      a: Visualization[X1, Y1],
      b: Visualization[X2, Y2],
    ): Visualization[X1 ∙ X2, Y1 ∙ Y2] =
      Par(a, b)
}
