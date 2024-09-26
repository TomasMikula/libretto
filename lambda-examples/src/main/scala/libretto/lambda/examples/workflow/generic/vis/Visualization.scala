package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*
import IOProportions.EdgeProportions

sealed trait Visualization[X, Y] {
  def ioProportions: IOProportions[X, Y]
  def length: Length

  def breadth: Breadth =
    ioProportions.totalBreadth

  def aspectRatio: AspectRatio =
    AspectRatio(length, breadth)
}

object Visualization {
  case class Unimplemented[X, Y](
    label: String,
    inEdge: EdgeDesc[X],
    outEdge: EdgeDesc[Y],
  ) extends Visualization[X, Y]:
    require(label.nonEmpty, "Label must not be empty string")

    override def length: Length = Length.one

    override def ioProportions: IOProportions[X, Y] =
      IOProportions.Separate(
        EdgeProportions.default(inEdge),
        EdgeProportions.default(outEdge),
      )

  case class Seq[X, Y1, Y2, Z](
    a: Visualization[X, Y1],
    m: Morph[Y1, Y2],
    b: Visualization[Y2, Z],
  ) extends Visualization[X, Z]:
    override def ioProportions: IOProportions[X, Z] =
      IOProportions.Separate(
        a.ioProportions.inEdge,
        b.ioProportions.outEdge,
      )

    override def length: Length =
      Length.cram(a.length, m.length, b.length)

  case class Par[∙[_, _], X1, X2, Y1, Y2](
    a: Visualization[X1, Y1],
    b: Visualization[X2, Y2],
  ) extends Visualization[X1 ∙ X2, Y1 ∙ Y2]:
    override def ioProportions: IOProportions[X1 ∙ X2, Y1 ∙ Y2] =
      IOProportions.Par(
        a.ioProportions,
        b.ioProportions,
      )

    override def length: Length =
      Length.max(a.length, b.length)

  case class ConnectorsOverlay[X, Y](
    base: Either[Visualization[X, Y], IOProportions[X, Y]],
    front: List[Connector[X, Y]],
  ) extends Visualization[X, Y] {
    override def ioProportions: IOProportions[X, Y] =
      base match
        case Left(vis) => vis.ioProportions
        case Right(props) => props

    override def length: Length =
      base match
        case Left(vis) => Length.max(vis.length, Length.one)
        case Right(props) => Length.one

  }

  def par[∙[_, _]]: ParBuilder[∙] =
    ParBuilder[∙]

  class ParBuilder[∙[_, _]]:
    def apply[X1, X2, Y1, Y2](
      a: Visualization[X1, Y1],
      b: Visualization[X2, Y2],
    ): Visualization[X1 ∙ X2, Y1 ∙ Y2] =
      Par(a, b)

  def connectors[X, Y](
    in: EdgeProportions[X],
    out: EdgeProportions[Y],
  )(
    connectors: Connector[X, Y]*
  ): Visualization[X, Y] =
    ConnectorsOverlay(
      Right(IOProportions.Separate(in, out)),
      connectors.toList,
    )

  def merge2[∙[_, _], X](x: EdgeProportions[X]): Visualization[X ∙ X, X] =
    connectors(
      EdgeProportions.Binary(x, x),
      x
    )(
      wiresOf(x)
        .flatMap { i =>
          List(
            Connector.Across(WirePick.Inl(i), i),
            Connector.Across(WirePick.Inr(i), i),
          )
        } *
    )

  private def wiresOf[X](x: EdgeProportions[X]): List[WirePick[X]] =
    x match
      case EdgeProportions.UnitWire =>
        WirePick.Id :: Nil
      case x: EdgeProportions.Binary[op, x1, x2] =>
        wiresOf(x.x1).map(_.inl[op, x2]) ++ wiresOf(x.x2).map(_.inr[op, x1])
}

