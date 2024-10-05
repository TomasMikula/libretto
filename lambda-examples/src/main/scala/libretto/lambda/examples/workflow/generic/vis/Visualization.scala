package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*
import scala.math.Ordering.Implicits.*

import Breadth.given
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

  case class WithBackgroundBox[X, Y](
    fill: Option[Color],
    stroke: Option[Color],
    front: Visualization[X, Y]
  ) extends Visualization[X, Y] {
    require(fill.nonEmpty || stroke.nonEmpty, "fill and stroke must not both be undefined")

    override def ioProportions: IOProportions[X, Y] =
      front.ioProportions

    override def length: Length =
      front.length
  }

  case class LabeledBox[X, Y](
    inEdge: EdgeDesc[X],
    outEdge: EdgeDesc[Y],
    label: String,
    fill: Option[Color],
  ) extends Visualization[X, Y] {
    require(label.nonEmpty, "Label must not be empty string")

    override def length: Length = Length.one

    override def ioProportions: IOProportions[X, Y] = {
      // 1 unit for each 4 characters
      val minBreadth = Breadth.cramNUnits(label.length / 4)

      val baseProps =
        IOProportions.Separate(
          EdgeProportions.default(inEdge),
          EdgeProportions.default(outEdge),
        )

      if (baseProps.totalBreadth < minBreadth)
        IOProportions.Weighted(minBreadth, baseProps)
      else
        baseProps
    }
  }

  case class Seq[X, Y1, Y2, Z](
    a: Visualization[X, Y1],
    m: Adaptoid[Y1, Y2],
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
    front: List[Connector[X, Y] | TrapezoidArea[X, Y]],
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

  case class Text[X, Y](
    value: String,
    ioProportions: IOProportions[X, Y],
    vpos: VPos,
  ) extends Visualization[X, Y] {
    override def length: Length = Length.one
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
    connectors: (Connector[X, Y] | TrapezoidArea[X, Y])*
  ): Visualization[X, Y] =
    ConnectorsOverlay(
      Right(IOProportions.Separate(in, out)),
      connectors.toList,
    )

  def connectors[X, Y](
    back: Visualization[X, Y],
  )(
    connectors: (Connector[X, Y] | TrapezoidArea[X, Y])*
  ): Visualization[X, Y] =
    ConnectorsOverlay(
      Left(back),
      connectors.toList,
    )

  def text[X, Y](value: String)(
    iProps: EdgeProportions[X],
    oProps: EdgeProportions[Y],
  ): Visualization[X, Y] =
    Text(value, IOProportions.Separate(iProps, oProps), VPos.Bottom)

  def merge2[∙[_, _], X](x: EdgeProportions[X]): Visualization[X ∙ X, X] =
    connectors(
      EdgeProportions.Binary(x, x),
      x
    )(
      wiresOf(x)
        .flatMap { i =>
          List(
            Connector.Across(i.inl, i),
            Connector.Across(i.inr, i),
          )
        } *
    )

  private def wiresOf[X](x: EdgeProportions[X]): List[WirePick[X]] =
    x match
      case EdgeProportions.UnitWire =>
        WirePick.pickId :: Nil
      case x: EdgeProportions.Binary[op, x1, x2] =>
        wiresOf(x.x1).map(_.inl[op, x2]) ++ wiresOf(x.x2).map(_.inr[op, x1])
}

