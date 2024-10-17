package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*
import libretto.lambda.util.TypeEq
import libretto.lambda.util.TypeEq.Refl
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

  def withBackground(fill: Color, stroke: Option[Color] = None): Visualization[X, Y]
}

object Visualization {
  /** Used to mark edges with flexible layout. Uninhabited, used only in phantom positions. */
  opaque type Flx <: Nothing = Nothing

  /** Witnesses that at lest one of the type parameters is [[Flx]]. */
  sealed trait Semiflex[-R, -S] {
    def tiltFst: Semiflex.OneSided[R, S] =
      this match
        case Semiflex.Both  => Semiflex.Fst()
        case t: Semiflex.OneSided[R, S] => t

    def tiltSnd: Semiflex.OneSided[R, S] =
      this match
        case Semiflex.Both  => Semiflex.Snd()
        case t: Semiflex.OneSided[R, S] => t
  }

  object Semiflex {
    sealed trait OneSided[-R, -S] extends Semiflex[R, S]

    case class Fst[S]() extends Semiflex.OneSided[Flx, S]
    case class Snd[R]() extends Semiflex.OneSided[R, Flx]
    case object Both extends Semiflex[Flx, Flx]

    given Semiflex[Flx, Flx] = Both
    given fst[S]: Semiflex[Flx, S] = Fst[S]()
    given snd[R]: Semiflex[R, Flx] = Snd[R]()
  }

  /** Visualization with flexibility markers ([[Flx]] or [[Rgd]]) of each edge (input and output). */
  sealed trait IVisualization[X, +R, +S, Y] extends Visualization[X, Y] {
    /** Trim any leading identity adaptation. */
    def trimIn: Option[Either[X =:= Y, IVisualization[X, ?, S, Y]]]

    /** Trim any trailing identity adaptation. */
    def trimOut: Option[Either[X =:= Y, IVisualization[X, R, ?, Y]]]

    /** Bring up possibly hidden input flexibility. */
    def flexiIn: Option[IVisualization[X, Flx, S, Y]]

    /** Bring up possibly hidden output flexibility. */
    def flexiOut: Option[IVisualization[X, R, Flx, Y]]

    override def withBackground(fill: Color, stroke: Option[Color]): Visualization[X, Y] =
      Visualization.WithBackgroundBox(Some(fill), stroke, this)
  }

  /** Visualization that is flexible in edge layout of both edges (input and output). */
  sealed trait Flexi[X, Y] extends IVisualization[X, Flx, Flx, Y] {
    override def flexiIn: Option[IVisualization[X, Flx, Flx, Y]] = Some(this)
    override def flexiOut: Option[IVisualization[X, Flx, Flx, Y]] = Some(this)
  }

  /** Visualization that is rigid in edge layout of both edges (input and output). */
  sealed trait Rigid[X, Y] extends IVisualization[X, ?, ?, Y] {
    override def flexiIn: Option[IVisualization[X, Flx, ?, Y]] = None // TODO: admit reorganization uncovering input flexibitlity
    override def flexiOut: Option[IVisualization[X, ?, Flx, Y]] = None // TODO: admit reorganization uncovering output flexibitlity
    override def trimIn: Option[Either[X =:= Y, IVisualization[X, ?, ?, Y]]] = None
    override def trimOut: Option[Either[X =:= Y, IVisualization[X, ?, ?, Y]]] = None
  }

  case class Unimplemented[X, Y](
    label: String,
    inEdge: EdgeDesc[X],
    outEdge: EdgeDesc[Y],
  ) extends Visualization.Flexi[X, Y] {
    require(label.nonEmpty, "Label must not be empty string")

    override def length: Length = Length.one

    override def ioProportions: IOProportions[X, Y] =
      IOProportions.Separate(
        EdgeProportions.default(inEdge),
        EdgeProportions.default(outEdge),
      )

    override def trimIn: Option[Either[X =:= Y, IVisualization[X, ?, Flx, Y]]] = None
    override def trimOut: Option[Either[X =:= Y, IVisualization[X, Flx, ?, Y]]] = None
  }
  case class WithBackgroundBox[X, R, S, Y](
    fill: Option[Color],
    stroke: Option[Color],
    front: IVisualization[X, R, S, Y]
  ) extends IVisualization[X, R, S, Y] {
    require(fill.nonEmpty || stroke.nonEmpty, "fill and stroke must not both be undefined")

    override def ioProportions: IOProportions[X, Y] =
      front.ioProportions

    override def length: Length =
      front.length

    override def flexiIn: Option[IVisualization[X, Flx, S, Y]] =
      front.flexiIn.map(WithBackgroundBox(fill, stroke, _))

    override def flexiOut: Option[IVisualization[X, R, Flx, Y]] =
      front.flexiOut.map(WithBackgroundBox(fill, stroke, _))

    override def trimIn: Option[Either[X =:= Y, IVisualization[X, ?, S, Y]]] =
      front.trimIn.map(_.map(WithBackgroundBox(fill, stroke, _)))

    override def trimOut: Option[Either[X =:= Y, IVisualization[X, R, ?, Y]]] =
      front.trimOut.map(_.map(WithBackgroundBox(fill, stroke, _)))
  }

  case class LabeledBox[X, Y](
    inEdge: EdgeDesc[X],
    outEdge: EdgeDesc[Y],
    label: String,
    fill: Option[Color],
  ) extends Visualization.Flexi[X, Y] {
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

    override def trimIn: Option[Either[X =:= Y, IVisualization[X, ?, Flx, Y]]] = None
    override def trimOut: Option[Either[X =:= Y, IVisualization[X, Flx, ?, Y]]] = None
  }

  sealed trait Sequence[X, +R, +S, Y] extends IVisualization[X, R, S, Y] {
    import Sequence.{Cons, Single}

    def size: Int
    def lengths: List[Length]

    override def length: Length =
      Length.cram(lengths*)

    def head: Visualization[X, ?]
    def last: Visualization[?, Y]

    override def flexiIn: Option[Sequence[X, Flx, S, Y]]
    override def flexiOut: Option[Sequence[X, R, Flx, Y]]
    override def trimIn: Option[Either[X =:= Y, Sequence[X, ?, S, Y]]]
    override def trimOut: Option[Either[X =:= Y, Sequence[X, R, ?, Y]]]

    def ::[W, P, Q](head: IVisualization[W, P, Q, X])(using Semiflex[Q, R]): Sequence[W, P, S, Y] =
      head.flexiOut match
        case None =>
          Cons(head, summon, this)
        case Some(h) =>
          this.trimIn match
            case Some(Left(TypeEq(Refl()))) => Single(h)
            case Some(Right(t))             => Cons(h, Semiflex.fst, t)
            case None =>
              this.flexiIn match
                case None => Cons(head, summon, this)
                case Some(t) =>
                  h.trimOut match
                    case None                       => Cons(head, summon, this)
                    case Some(Left(TypeEq(Refl()))) => t
                    case Some(Right(h))             => Cons(h, Semiflex.snd, t)

    def ::[W](head: Visualization[W, X])(using ev: R <:< Flx): Sequence[W, ?, S, Y] =
      head match
        case v: IVisualization[W, p, q, X] =>
          given Semiflex[q, R] = ev.substituteContra(Semiflex.Snd[q]())
          v :: this
  }

  object Sequence {

    case class Single[X, R, S, Y](
      elem: IVisualization[X, R, S, Y],
    ) extends Sequence[X, R, S, Y] {
      override def size = 1
      override def lengths: List[Length] = List(elem.length)

      override def ioProportions: IOProportions[X, Y] =
        elem.ioProportions

      override def head = elem
      override def last = elem

      override def trimIn: Option[Either[X =:= Y, Sequence[X, ?, S, Y]]] = elem.trimIn.map(_.map(Single(_)))
      override def trimOut: Option[Either[X =:= Y, Sequence[X, R, ?, Y]]] = elem.trimOut.map(_.map(Single(_)))

      override def flexiIn: Option[Sequence[X, Flx, S, Y]] = elem.flexiIn.map(Single(_))
      override def flexiOut: Option[Sequence[X, R, Flx, Y]] = elem.flexiOut.map(Single(_))
    }

    case class Cons[X, P, Q, Y, R, S, Z](
      head: IVisualization[X, P, Q, Y],
      flx: Semiflex[Q, R],
      tail: Sequence[Y, R, S, Z],
    ) extends Sequence[X, P, S, Z] {
      override lazy val size = 1 + tail.size
      override lazy val lengths: List[Length] = head.length :: tail.lengths

      override def last = tail.last

      override def ioProportions: IOProportions[X, Z] =
        IOProportions.Separate(head.ioProportions.inEdge, last.ioProportions.outEdge)

      override def flexiIn: Option[Sequence[X, Flx, S, Z]] =
        head.flexiIn.map(Cons(_, flx, tail))

      override def flexiOut: Option[Sequence[X, P, Flx, Z]] =
        tail.flexiOut.map(Cons(head, flx, _))

      override def trimIn: Option[Either[X =:= Z, Sequence[X, ?, S, Z]]] =
        head.trimIn match
          case Some(Left(TypeEq(Refl()))) => Some(Right(tail))
          case Some(Right(h))             => Some(Right(Cons(h, flx, tail)))
          case None                       => None

      override def trimOut: Option[Either[X =:= Z, Sequence[X, P, ?, Z]]] =
        tail.trimOut match
          case Some(Left(TypeEq(Refl()))) => Some(Right(Single(head)))
          case Some(Right(t))             => Some(Right(Cons(head, flx, t)))
          case None                       => None
    }

    def apply[X, Y](
      v: Visualization[X, Y],
    ): Sequence[X, ?, ?, Y] =
      v match { case v: IVisualization[X, r, s, Y] => Single(v) }

    def apply[X, Y, Z](
      v1: Visualization.Flexi[X, Y],
      v2: Visualization[Y, Z],
    ): Sequence[X, Flx, ?, Z] =
      v1 :: Sequence(v2)

    def apply[X, Y, Z](
      v1: Visualization[X, Y],
      v2: Visualization.Flexi[Y, Z],
    ): Sequence[X, ?, Flx, Z] =
      v1 :: Single(v2)

    def apply[W, X, Y, Z](
      v1: Visualization[W, X],
      v2: Visualization.Flexi[X, Y],
      v3: Visualization[Y, Z],
    ): Sequence[W, ?, ?, Z] =
      v1 :: v2 :: Sequence(v3)

    def apply[W, X, Y, Z](
      v1: Visualization.Flexi[W, X],
      v2: Visualization[X, Y],
      v3: Visualization.Flexi[Y, Z],
    ): Sequence[W, Flx, Flx, Z] =
      v1 :: v2 :: Single(v3)
  }

  case class Adapt[X, Y](f: Adaptoid[X, Y]) extends Visualization.Flexi[X, Y] {
    override def length: Length = f.length
    override def ioProportions: IOProportions[X, Y] =
      IOProportions.Separate(
        EdgeProportions.default(f.inDesc),
        EdgeProportions.default(f.outDesc),
      )

    override def trimIn: Option[Either[X =:= Y, IVisualization[X, ?, Flx, Y]]] =
      f match
        case Adaptoid.Id(_) => Some(Left(summon))
        case _              => None

    override def trimOut: Option[Either[X =:= Y, IVisualization[X, Flx, ?, Y]]] =
      f match
        case Adaptoid.Id(_) => Some(Left(summon))
        case _              => None
  }

  case class Par[∙[_, _], X1, X2, Y1, Y2](
    op: OpTag[∙],
    a: Visualization[X1, Y1],
    b: Visualization[X2, Y2],
  ) extends Visualization.Rigid[X1 ∙ X2, Y1 ∙ Y2]:
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

    override def trimIn: Option[Either[X =:= Y, IVisualization[X, ?, Flx, Y]]] = None
    override def trimOut: Option[Either[X =:= Y, IVisualization[X, Flx, ?, Y]]] = None
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

    override def trimIn: Option[Either[X =:= Y, IVisualization[X, ?, Flx, Y]]] = None
    override def trimOut: Option[Either[X =:= Y, IVisualization[X, Flx, ?, Y]]] = None
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
