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

    override def length: Length =
      Length.cram(lengths*)

    def head: Visualization[X, ?]
    def last: Visualization[?, Y]

    def ::[W](head: Visualization.Flexi[W, X]): Sequence.FlexiHead[W, Y]
  }

  object Sequence {
    sealed trait FlexiHead[X, Y] extends Sequence[X, Y] {
      def ::[W](head: Visualization[W, X]): Sequence[W, Y]
    }

    case class Single[X, Y](
      elem: Visualization[X, Y],
    ) extends Sequence[X, Y] {
      override def size = 1
      override def lengths: List[Length] = List(elem.length)

      override def ioProportions: IOProportions[X, Y] =
        elem.ioProportions

      override def head = elem
      override def last = elem

      override def ::[W](head: Visualization.Flexi[W, X]): Sequence.FlexiHead[W, Y] =
        (head, elem) match
          case (Adapt(Adaptoid.Id(_)), el: Flexi[X, Y]) => SingleFlexi(el)
          case (head, Adapt(Adaptoid.Id(_)))            => SingleFlexi(head)
          case _                                        => ConsFlexiHead(head, this)
          // TODO: also look if elem is a sequence with flexi head
    }

    case class SingleFlexi[X, Y](
      elem: Visualization.Flexi[X, Y],
    ) extends Sequence.FlexiHead[X, Y] {
      override def size = 1
      override def lengths: List[Length] = List(elem.length)

      override def ioProportions: IOProportions[X, Y] =
        elem.ioProportions

      override def head = elem
      override def last = elem

      override def ::[W](head: Flexi[W, X]): FlexiHead[W, Y] =
        head :: Single(elem)

      override def ::[W](head: Visualization[W, X]): Sequence[W, Y] =
        (head, elem) match
          case (Adapt(Adaptoid.Id(_)), elem)           => this
          case (h: Flexi[W, X], Adapt(Adaptoid.Id(_))) => SingleFlexi(h)
          case _                                       => Cons(head, this)
          // TODO: also look if head is a sequence with flexi/Adaptoid last elem
    }

    sealed trait Multi[X, Y] extends Sequence[X, Y] {
      override def ioProportions: IOProportions[X, Y] =
        IOProportions.Separate(head.ioProportions.inEdge, last.ioProportions.outEdge)
    }

    case class Cons[X, Y, Z](
      head: Visualization[X, Y],
      tail: Sequence.FlexiHead[Y, Z],
    ) extends Sequence.Multi[X, Z] {
      override lazy val size = 1 + tail.size
      override lazy val lengths: List[Length] = head.length :: tail.lengths

      override def last = tail.last

      override def ::[W](h0: Flexi[W, X]): FlexiHead[W, Z] =
        (h0, head) match
          case (Adapt(Adaptoid.Id(_)), h1: Flexi[X, Y]) => ConsFlexiHead(h1, tail)
          case (h0, Adapt(Adaptoid.Id(_)))              => ConsFlexiHead(h0, tail)
          case _                                        => ConsFlexiHead(h0, this)
          // TODO: also look if head is a sequence with flexi/Adaptoid head
    }

    case class ConsFlexiHead[X, Y, Z](
      head: Visualization.Flexi[X, Y],
      tail: Sequence[Y, Z],
    ) extends Sequence.FlexiHead[X, Z] with Sequence.Multi[X, Z] {
      override lazy val size = 1 + tail.size
      override lazy val lengths: List[Length] = head.length :: tail.lengths

      override def last = tail.last

      override def ::[W](h0: Flexi[W, X]): FlexiHead[W, Z] =
        (h0, head) match
          case (Adapt(Adaptoid.Id(_)), _)  => this
          case (h0, Adapt(Adaptoid.Id(_))) => ConsFlexiHead(h0, tail)
          case _                           => ConsFlexiHead(h0, this)

      override def ::[W](h0: Visualization[W, X]): Sequence[W, Z] =
        (h0, head) match
          case (Adapt(Adaptoid.Id(_)), h1)              => this
          case (h0: Flexi[W, X], Adapt(Adaptoid.Id(_))) => ConsFlexiHead(h0, tail)
          case _                                        => Cons(h0, this)
          // TODO: also look if h0 is a sequence with flexi/Adaptoid last elem
    }

    def apply[X, Y, Z](
      v1: Visualization.Flexi[X, Y],
      v2: Visualization[Y, Z],
    ): Sequence.FlexiHead[X, Z] =
      v1 :: Single(v2)

    def apply[X, Y, Z](
      v1: Visualization[X, Y],
      v2: Visualization.Flexi[Y, Z],
    ): Sequence[X, Z] =
      v1 :: SingleFlexi(v2)

    def apply[W, X, Y, Z](
      v1: Visualization[W, X],
      v2: Visualization.Flexi[X, Y],
      v3: Visualization[Y, Z],
    ): Sequence[W, Z] =
      v1 :: v2 :: Single(v3)

    def apply[W, X, Y, Z](
      v1: Visualization.Flexi[W, X],
      v2: Visualization[X, Y],
      v3: Visualization.Flexi[Y, Z],
    ): Sequence.FlexiHead[W, Z] =
      v1 :: v2 :: SingleFlexi(v3)
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
    op: OpTag[∙],
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
    base: Either[Visualization.Flexi[X, Y], (EdgeDesc[X], EdgeDesc[Y])],
    front: List[Connector[X, Y] | TrapezoidArea[X, Y]],
  ) extends Visualization.Flexi[X, Y] {
    override def ioProportions: IOProportions[X, Y] =
      base match
        case Left(vis) => vis.ioProportions
        case Right((x, y)) => IOProportions.Separate(EdgeProportions.default(x), EdgeProportions.default(y))

    override def length: Length =
      base match
        case Left(vis) => Length.max(vis.length, Length.one)
        case Right(props) => Length.one
  }

  case class Text[X, Y](
    value: String,
    in: EdgeDesc[X],
    out: EdgeDesc[Y],
    vpos: VPos,
  ) extends Visualization.Flexi[X, Y] {
    override def length: Length = Length.one

    override def ioProportions: IOProportions[X, Y] =
      IOProportions.Separate(EdgeProportions.default(in), EdgeProportions.default(out))
  }

  def par[∙[_, _]](using OpTag[∙]): ParBuilder[∙] =
    ParBuilder[∙]

  class ParBuilder[∙[_, _]](using op: OpTag[∙]):
    def apply[X1, X2, Y1, Y2](
      a: Visualization[X1, Y1],
      b: Visualization[X2, Y2],
    ): Visualization[X1 ∙ X2, Y1 ∙ Y2] =
      Par(op, a, b)

  def connectors[X, Y](
    in: EdgeDesc[X],
    out: EdgeDesc[Y],
  )(
    connectors: (Connector[X, Y] | TrapezoidArea[X, Y])*
  ): Visualization.Flexi[X, Y] =
    ConnectorsOverlay(
      Right((in, out)),
      connectors.toList,
    )

  def connectors[X, Y](
    back: Visualization.Flexi[X, Y],
  )(
    connectors: (Connector[X, Y] | TrapezoidArea[X, Y])*
  ): Visualization.Flexi[X, Y] =
    ConnectorsOverlay(
      Left(back),
      connectors.toList,
    )

  def text[X, Y](value: String)(
    iDesc: EdgeDesc[X],
    oDesc: EdgeDesc[Y],
  ): Visualization.Flexi[X, Y] =
    Text(value, iDesc, oDesc, VPos.Bottom)
}

