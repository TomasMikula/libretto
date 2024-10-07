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

  def withBackground(fill: Color, stroke: Option[Color] = None): Visualization[X, Y] =
    Visualization.WithBackgroundBox(Some(fill), stroke, this)
}

object Visualization {
  /** Visualization that is flexible in edge layout of both edges (input and output). */
  sealed trait Flexi[X, Y] extends Visualization[X, Y]

  case class Unimplemented[X, Y](
    label: String,
    inEdge: EdgeDesc[X],
    outEdge: EdgeDesc[Y],
  ) extends Visualization.Flexi[X, Y]:
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

  sealed trait Sequence[X, Y] extends Visualization[X, Y] {
    def size: Int
    def lengths: List[Length]

    protected def inProportions: EdgeProportions[X]
    protected def outProportions: EdgeProportions[Y]

    override def length: Length =
      Length.cram(lengths*)

    override def ioProportions: IOProportions[X, Y] =
      IOProportions.Separate(inProportions, outProportions)

    def ::[W](head: Visualization.Flexi[W, X]): Sequence.FlexiHead[W, Y] =
      Sequence.ConsFlexiHead(head, this)
  }

  object Sequence {
    sealed trait FlexiHead[X, Y] extends Sequence[X, Y] {
      def ::[W](head: Visualization[W, X]): Sequence[W, Y] =
        Cons(head, this)
    }

    case class Two[X, Y, Z](
      fst: Visualization[X, Y],
      snd: Visualization.Flexi[Y, Z],
    ) extends Sequence[X, Z] {
      override def size = 2
      override def lengths: List[Length] = List(fst.length, snd.length)

      override protected def inProportions: EdgeProportions[X] = fst.ioProportions.inEdge
      override protected def outProportions: EdgeProportions[Z] = snd.ioProportions.outEdge
    }

    case class TwoFlexiFst[X, Y, Z](
      fst: Visualization.Flexi[X, Y],
      snd: Visualization[Y, Z],
    ) extends Sequence.FlexiHead[X, Z] {
      override def size = 2
      override def lengths: List[Length] = List(fst.length, snd.length)

      override protected def inProportions: EdgeProportions[X] = fst.ioProportions.inEdge
      override protected def outProportions: EdgeProportions[Z] = snd.ioProportions.outEdge
    }

    case class Cons[X, Y, Z](
      head: Visualization[X, Y],
      tail: Sequence.FlexiHead[Y, Z],
    ) extends Sequence[X, Z] {
      override lazy val size = 1 + tail.size
      override lazy val lengths: List[Length] = head.length :: tail.lengths

      override protected def inProportions: EdgeProportions[X] = head.ioProportions.inEdge
      override protected def outProportions: EdgeProportions[Z] = tail.outProportions
    }

    case class ConsFlexiHead[X, Y, Z](
      head: Visualization.Flexi[X, Y],
      tail: Sequence[Y, Z],
    ) extends Sequence.FlexiHead[X, Z] {
      override lazy val size = 1 + tail.size
      override lazy val lengths: List[Length] = head.length :: tail.lengths

      override protected def inProportions: EdgeProportions[X] = head.ioProportions.inEdge
      override protected def outProportions: EdgeProportions[Z] = tail.outProportions
    }

    def apply[X, Y, Z](
      v1: Visualization.Flexi[X, Y],
      v2: Visualization[Y, Z],
    ): Sequence.FlexiHead[X, Z] =
      TwoFlexiFst(v1, v2)

    def apply[X, Y, Z](
      v1: Visualization[X, Y],
      v2: Visualization.Flexi[Y, Z],
    ): Sequence[X, Z] =
      Two(v1, v2)

    def apply[W, X, Y, Z](
      v1: Visualization[W, X],
      v2: Visualization.Flexi[X, Y],
      v3: Visualization[Y, Z],
    ): Sequence[W, Z] =
      v1 :: TwoFlexiFst(v2, v3)

    def apply[W, X, Y, Z](
      v1: Visualization.Flexi[W, X],
      v2: Visualization[X, Y],
      v3: Visualization.Flexi[Y, Z],
    ): Sequence.FlexiHead[W, Z] =
      v1 :: Two(v2, v3)
  }

  case class Adapt[X, Y](f: Adaptoid[X, Y]) extends Visualization.Flexi[X, Y] {
    override def length: Length = f.length
    override def ioProportions: IOProportions[X, Y] =
      IOProportions.Separate(
        EdgeProportions.default(f.inDesc),
        EdgeProportions.default(f.outDesc),
      )
  }

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

