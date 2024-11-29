package libretto.lambda.examples.workflow.generic.vis

import libretto.{lambda as ll}
import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*
import libretto.lambda.util.TypeEq
import libretto.lambda.util.TypeEq.Refl
import scala.annotation.tailrec
import scala.collection.immutable.{:: as NonEmptyList}
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

  def indexed: Visualization.IVisualization[X, ?, ?, ?, Y]
}

object Visualization {
  /** Used to mark edges with flexible layout. Uninhabited, used only in phantom positions. */
  opaque type Flx <: Nothing = Nothing

  /** Used to mark visualizations that can be skewed horixontally. */
  opaque type Skw <: Nothing = Nothing

  /** Witnesses that at least one of the type parameters is [[Flx]]. */
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

  /** Visualization with markers of
   *
   * - flexibility, for input and output edge separately
   * - horizontal skewability
   *
   * @tparam X the input edge
   * @tparam R flexibility of the input edge ([[Flx]] for flexible, anything else otherwise)
   * @tparam J horizontal skewability ([[Skw]] for skewable, anything else otherwise)
   * @tparam S flexibility of the output edge ([[Flx]] for flexible, anything else otherwise)
   * @tparam Y the output edge
   */
  sealed trait IVisualization[X, +R, +J, +S, Y] extends Visualization[X, Y] {
    override def indexed: IVisualization[X, R, J, S, Y] = this

    /** Trim any leading identity adaptation. */
    def trimIn: Option[Either[(X =:= Y, EdgeDesc[Y]), IVisualization[X, ?, J, S, Y]]]

    /** Trim any trailing identity adaptation. */
    def trimOut: Option[Either[(X =:= Y, EdgeDesc[Y]), IVisualization[X, R, J, ?, Y]]]

    /** Bring up possibly hidden input flexibility. */
    def flexiIn: Option[IVisualization[X, Flx, J, S, Y]]

    /** Bring up possibly hidden output flexibility. */
    def flexiOut: Option[IVisualization[X, R, J, Flx, Y]]

    /** Bring up possibly hidden skewability. */
    def skewable: Option[IVisualization[X, R, Skw, S, Y]]

    override def withBackground(fill: Color, stroke: Option[Color]): Visualization[X, Y] =
      Visualization.WithBackgroundBox(Some(fill), stroke, this)
  }

  /** Visualization that is flexible in edge layout of both edges (input and output). */
  sealed trait Flexi[X, J, Y] extends IVisualization[X, Flx, J, Flx, Y] {
    override def flexiIn: Option[IVisualization[X, Flx, J, Flx, Y]] = Some(this)
    override def flexiOut: Option[IVisualization[X, Flx, J, Flx, Y]] = Some(this)
  }

  type FullyFlexi[X, Y] = Flexi[X, Skw, Y]

  case class Unimplemented[X, Y](
    label: String,
    inEdge: EdgeDesc[X],
    outEdge: EdgeDesc[Y],
  ) extends Visualization.Flexi[X, ?, Y] {
    require(label.nonEmpty, "Label must not be empty string")

    override def length: Length = Length.one

    override def ioProportions: IOProportions[X, Y] =
      IOProportions.Separate(
        EdgeProportions.default(inEdge),
        EdgeProportions.default(outEdge),
      )

    override def trimIn = None
    override def trimOut = None
    override def skewable = None
  }
  case class WithBackgroundBox[X, R, S, Y](
    fill: Option[Color],
    stroke: Option[Color],
    front: IVisualization[X, R, ?, S, Y]
  ) extends IVisualization[X, R, ?, S, Y] {
    require(fill.nonEmpty || stroke.nonEmpty, "fill and stroke must not both be undefined")

    override def ioProportions: IOProportions[X, Y] =
      front.ioProportions

    override def length: Length =
      front.length

    override def flexiIn: Option[IVisualization[X, Flx, ?, S, Y]] =
      front.flexiIn.map(WithBackgroundBox(fill, stroke, _))

    override def flexiOut: Option[IVisualization[X, R, ?, Flx, Y]] =
      front.flexiOut.map(WithBackgroundBox(fill, stroke, _))

    override def skewable: Option[IVisualization[X, R, Skw, S, Y]] =
      None

    override def trimIn: Option[Either[(X =:= Y, EdgeDesc[Y]), IVisualization[X, ?, ?, S, Y]]] =
      front.trimIn.map(_.map(WithBackgroundBox(fill, stroke, _)))

    override def trimOut: Option[Either[(X =:= Y, EdgeDesc[Y]), IVisualization[X, R, ?, ?, Y]]] =
      front.trimOut.map(_.map(WithBackgroundBox(fill, stroke, _)))
  }

  case class LabeledBox[X, Y](
    inEdge: EdgeDesc[X],
    outEdge: EdgeDesc[Y],
    label: String,
    fill: Option[Color],
  ) extends Visualization.Flexi[X, ?, Y] {
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

    override def trimIn = None
    override def trimOut = None
    override def skewable = None
  }

  sealed trait Sequence[X, +R, +S, Y] extends IVisualization[X, R, ?, S, Y] {
    import Sequence.{Cons, Single}

    def size: Int
    def lengths: List[Length]

    override def length: Length =
      Length.cram(lengths*)

    def head: Visualization[X, ?]
    def last: Visualization[?, Y]

    override def flexiIn: Option[Sequence[X, Flx, S, Y]]
    override def flexiOut: Option[Sequence[X, R, Flx, Y]]
    override def trimIn: Option[Either[(X =:= Y, EdgeDesc[Y]), Sequence[X, ?, S, Y]]]
    override def trimOut: Option[Either[(X =:= Y, EdgeDesc[Y]), Sequence[X, R, ?, Y]]]

    // skewing sequences is not supported
    override def skewable: Option[IVisualization[X, R, Skw, S, Y]] = None

    def ::[W, P, Q](head: IVisualization[W, P, ?, Q, X])(using
      flx: Semiflex[Q, R],
    ): Sequence[W, P, S, Y] = {
      flx.tiltFst match
        case Semiflex.Fst() =>
          summon[Q =:= Flx]
          this.trimIn match
            case Some(Left((TypeEq(Refl()), _))) =>
              Single(head)
            case Some(Right(t)) =>
              Cons(head, Semiflex.fst, t)
              // TODO: try to also trim from head
            case None =>
              this.flexiIn match
                case None => Cons(head, summon, this)
                case Some(t) =>
                  head.trimOut match
                    case None                            => Cons(head, summon, this)
                    case Some(Left((TypeEq(Refl()), _))) => t
                    case Some(Right(h))                  => Cons(h, Semiflex.snd, t)
        case Semiflex.Snd() =>
          summon[R =:= Flx]
          head.trimOut match
            case Some(Left((TypeEq(Refl()), _))) =>
              this
            case Some(Right(h)) =>
              Cons(h, Semiflex.snd, this)
              // TODO: try to also trim from this
            case None =>
              head.flexiOut match
                case None => Cons(head, summon, this)
                case Some(h) =>
                  this.trimIn match
                    case None                            => Cons(head, summon, this)
                    case Some(Left((TypeEq(Refl()), _))) => Single(h)
                    case Some(Right(t))                  => Cons(h, Semiflex.fst, t)
    }

    def ::[W](head: Visualization[W, X])(using ev: R <:< Flx): Sequence[W, ?, S, Y] =
      head match
        case v: IVisualization[W, p, j, q, X] =>
          given Semiflex[q, R] = ev.substituteContra(Semiflex.Snd[q]())
          v :: this
  }

  object Sequence {

    case class Single[X, R, S, Y](
      elem: IVisualization[X, R, ?, S, Y],
    ) extends Sequence[X, R, S, Y] {
      override def size = 1
      override def lengths: List[Length] = List(elem.length)

      override def ioProportions: IOProportions[X, Y] =
        elem.ioProportions

      override def head = elem
      override def last = elem

      override def trimIn: Option[Either[(X =:= Y, EdgeDesc[Y]), Sequence[X, ?, S, Y]]] = elem.trimIn.map(_.map(Single(_)))
      override def trimOut: Option[Either[(X =:= Y, EdgeDesc[Y]), Sequence[X, R, ?, Y]]] = elem.trimOut.map(_.map(Single(_)))

      override def flexiIn: Option[Sequence[X, Flx, S, Y]] = elem.flexiIn.map(Single(_))
      override def flexiOut: Option[Sequence[X, R, Flx, Y]] = elem.flexiOut.map(Single(_))
    }

    case class Cons[X, P, Q, Y, R, S, Z](
      head: IVisualization[X, P, ?, Q, Y],
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

      override def trimIn: Option[Either[(X =:= Z, EdgeDesc[Z]), Sequence[X, ?, S, Z]]] =
        head.trimIn match
          case Some(Left((TypeEq(Refl()), _))) => Some(Right(tail))
          case Some(Right(h))                  => Some(Right(Cons(h, flx, tail)))
          case None                            => None

      override def trimOut: Option[Either[(X =:= Z, EdgeDesc[Z]), Sequence[X, P, ?, Z]]] =
        tail.trimOut match
          case Some(Left((TypeEq(Refl()), _))) => Some(Right(Single(head)))
          case Some(Right(t))                  => Some(Right(Cons(head, flx, t)))
          case None                            => None
    }

    def apply[X, P, I, Q, Y](
      v: IVisualization[X, P, I, Q, Y],
    ): Sequence[X, P, Q, Y] =
      Single(v)

    def apply[X, Y](
      v: Visualization[X, Y],
    ): Sequence[X, ?, ?, Y] =
      apply(v.indexed)

    def apply[X, Y, Z](
      v1: Visualization.Flexi[X, ?, Y],
      v2: Visualization[Y, Z],
    ): Sequence[X, Flx, ?, Z] =
      v1 :: Sequence(v2)

    def apply[X, Y, Z](
      v1: Visualization[X, Y],
      v2: Visualization.Flexi[Y, ?, Z],
    ): Sequence[X, ?, Flx, Z] =
      v1 :: Single(v2)

    def apply[W, X, Y, Z](
      v1: Visualization[W, X],
      v2: Visualization.Flexi[X, ?, Y],
      v3: Visualization[Y, Z],
    ): Sequence[W, ?, ?, Z] =
      v1 :: v2 :: Sequence(v3)

    def apply[W, X, Y, Z](
      v1: Visualization.Flexi[W, ?, X],
      v2: Visualization[X, Y],
      v3: Visualization.Flexi[Y, ?, Z],
    ): Sequence[W, Flx, Flx, Z] =
      v1 :: v2 :: Single(v3)
  }

  case class Adapt[X, Y](f: Adaptoid[X, Y]) extends Visualization.FullyFlexi[X, Y] {
    override def length: Length = f.length
    override def ioProportions: IOProportions[X, Y] =
      IOProportions.Separate(
        EdgeProportions.default(f.inDesc),
        EdgeProportions.default(f.outDesc),
      )

    override def skewable: Option[IVisualization[X, Flx, Skw, Flx, Y]] =
      Some(this)

    override def trimIn: Option[Either[(X =:= Y, EdgeDesc[Y]), IVisualization[X, ?, Skw, Flx, Y]]] =
      f match
        case Adaptoid.Id(d) => Some(Left((summon, d)))
        case _              => None

    override def trimOut: Option[Either[(X =:= Y, EdgeDesc[Y]), IVisualization[X, Flx, Skw, ?, Y]]] =
      f match
        case Adaptoid.Id(d) => Some(Left((summon, d)))
        case _              => None
  }

  sealed trait Par[∙[_, _], X1, X2, Y1, Y2] extends Visualization[X1 ∙ X2, Y1 ∙ Y2] {
    override def indexed: IPar[∙, X1, ?, ?, ?, Y1, X2, ?, ?, ?, Y2]
  }

  case class IPar[∙[_, _], X1, P, I, Q, Y1, X2, R, J, S, Y2](
    op: OpTag[∙],
    a: IVisualization[X1, P, I, Q, Y1],
    b: IVisualization[X2, R, J, S, Y2],
  ) extends Par[∙, X1, X2, Y1, Y2] with IVisualization[
    X1 ∙ X2,
    P | R | I | J, // input is flexible if components' inputs are flexible (P, R) and both components are skewable (I, J)
    I | J,         // skewable if both components are skewable
    Q | S | I | J, // output is flexible if components' outputs are flexible (Q, S) and both components are skewable (I, J)
    Y1 ∙ Y2,
  ] {
    type FlI = P | R | I | J
    type FlO = Q | S | I | J
    type Sk  = I | J

    private given OpTag[∙] = op

    override def indexed: IPar[∙, X1, P, I, Q, Y1, X2, R, J, S, Y2] = this

    override def ioProportions: IOProportions[X1 ∙ X2, Y1 ∙ Y2] =
      IOProportions.Par(
        a.ioProportions,
        b.ioProportions,
      )

    override def length: Length =
      Length.max(a.length, b.length)

    override def flexiIn: Option[IVisualization[X1 ∙ X2, Flx, Sk, FlO, Y1 ∙ Y2]] =
      for
        a <- a.flexiIn.flatMap(_.skewable)
        b <- b.flexiIn.flatMap(_.skewable)
      yield
        IPar(op, a, b)

    override def flexiOut: Option[IVisualization[X1 ∙ X2, FlI, Sk, Flx, Y1 ∙ Y2]] =
      for
        a <- a.flexiOut.flatMap(_.skewable)
        b <- b.flexiOut.flatMap(_.skewable)
      yield
        IPar(op, a, b)

    override def skewable: Option[IPar[∙, X1, P, Skw, Q, Y1, X2, R, Skw, S, Y2]] =
      for
        a <- a.skewable
        b <- b.skewable
      yield
        IPar(op, a, b)

    override def trimIn: Option[Either[
      ((X1 ∙ X2) =:= (Y1 ∙ Y2), EdgeDesc[Y1 ∙ Y2]),
      IVisualization[X1 ∙ X2, ?, Sk, FlO, Y1 ∙ Y2]
    ]] =
      (a.trimIn, b.trimIn) match
        case (Some(Right(a))                 , Some(Right(b)))                  => Some(Right(IPar(op, a, b)))
        case (Some(Right(a))                 , Some(Left((TypeEq(Refl()), d)))) => Some(Right(IPar(op, a, Adapt(Adaptoid.Id(d)))))
        case (Some(Left((TypeEq(Refl()), c))), Some(Right(b)))                  => Some(Right(IPar(op, Adapt(Adaptoid.Id(c)), b)))
        case (Some(Left((TypeEq(Refl()), c))), Some(Left((TypeEq(Refl()), d)))) => Some(Left((summon, c ∙ d)))
        case (Some(Right(a))                 , None)                            => Some(Right(IPar(op, a, b)))
        case (None                           , Some(Right(b)))                  => Some(Right(IPar(op, a, b)))
        case (Some(Left(_)), None) => None // cannot report as progress
        case (None, Some(Left(_))) => None // cannot report as progress
        case (None, None) => None

    override def trimOut: Option[Either[
      ((X1 ∙ X2) =:= (Y1 ∙ Y2), EdgeDesc[Y1 ∙ Y2]),
      IVisualization[X1 ∙ X2, FlI, Sk, ?, Y1 ∙ Y2]
    ]] =
      (a.trimOut, b.trimOut) match
        case (Some(Right(a))                 , Some(Right(b)))                  => Some(Right(IPar(op, a, b)))
        case (Some(Right(a))                 , Some(Left((TypeEq(Refl()), d)))) => Some(Right(IPar(op, a, Adapt(Adaptoid.Id(d)))))
        case (Some(Left((TypeEq(Refl()), c))), Some(Right(b)))                  => Some(Right(IPar(op, Adapt(Adaptoid.Id(c)), b)))
        case (Some(Left((TypeEq(Refl()), c))), Some(Left((TypeEq(Refl()), d)))) => Some(Left((summon, c ∙ d)))
        case (Some(Right(a))                 , None)                            => Some(Right(IPar(op, a, b)))
        case (None                           , Some(Right(b)))                  => Some(Right(IPar(op, a, b)))
        case (Some(Left(_)), None) => None // cannot report as progress
        case (None, Some(Left(_))) => None // cannot report as progress
        case (None, None) => None
  }

  case class IParN[Wrap[_], X, P, I, Q, Y](
    op: OpTag[Wrap],
    components: IParN.Components[X, P, I, Q, Y],
  ) extends IVisualization[Wrap[X], P, I, Q, Wrap[Y]] {
    override def ioProportions: IOProportions[Wrap[X], Wrap[Y]] =
      IOProportions.ParN(components.ioProportions)

    override def length: Length =
      components.lengths.reduce(Length.max)

    override def flexiIn: Option[IVisualization[Wrap[X], Flx, I, Q, Wrap[Y]]] =
      components.flexiIn.map(IParN(op, _))

    override def flexiOut: Option[IVisualization[Wrap[X], P, I, Flx, Wrap[Y]]] =
      components.flexiOut.map(IParN(op, _))

    override def skewable: Option[IParN[Wrap, X, P, Skw, Q, Y]] =
      components.skewable.map(IParN(op, _))

    override def trimIn: Option[Either[
      (Wrap[X] =:= Wrap[Y], EdgeDesc[Wrap[Y]]),
      IVisualization[Wrap[X], ?, I, Q, Wrap[Y]]
    ]] =
      components.trimIn.map[Either[
        (Wrap[X] =:= Wrap[Y], EdgeDesc[Wrap[Y]]),
        IVisualization[Wrap[X], ?, I, Q, Wrap[Y]]
      ]] {
        case Left((TypeEq(Refl()), comps)) => Left((summon, EdgeDesc.TupleN(op, comps)))
        case Right(comps) => Right(IParN(op, comps))
      }

    override def trimOut: Option[Either[
      (Wrap[X] =:= Wrap[Y], EdgeDesc[Wrap[Y]]),
      IVisualization[Wrap[X], P, I, ?, Wrap[Y]]
    ]] =
      components.trimOut.map[Either[
        (Wrap[X] =:= Wrap[Y], EdgeDesc[Wrap[Y]]),
        IVisualization[Wrap[X], P, I, ?, Wrap[Y]]
      ]] {
        case Left((TypeEq(Refl()), comps)) => Left((summon, EdgeDesc.TupleN(op, comps)))
        case Right(comps) => Right(IParN(op, comps))
      }
  }

  object IParN {
    sealed trait Components[X, +P, +I, +Q, Y] {
      def ioProportions: IOProportions.ParN.Components[X, Y]

      def size: Int

      def lengths: NonEmptyList[Length] =
        lengths(Nil)

      @tailrec
      private def lengths(tailAcc: List[Length]): NonEmptyList[Length] =
        this match
          case Single(vis) => NonEmptyList(vis.length, tailAcc)
          case Snoc(init, last) => init.lengths(last.length :: tailAcc)

      def flexiIn: Option[Components[X, Flx, I, Q, Y]]

      def flexiOut: Option[Components[X, P, I, Flx, Y]]

      def skewable: Option[Components[X, P, Skw, Q, Y]]

      def trimIn: Option[Either[
        (X =:= Y, EdgeDesc.TupleN.Components[Y]),
        Components[X, ?, I, Q, Y]
      ]]

      def trimOut: Option[Either[
        (X =:= Y, EdgeDesc.TupleN.Components[Y]),
        Components[X, P, I, ?, Y]
      ]]

      def nonEmpty[R](f: [x1, x2, y1, y2] => (X =:= (x1, x2), Y =:= (y1, y2)) ?=> R): R

      final def nonEmptyIn [R](f: [x1, x2] => (X =:= (x1, x2)) ?=> R): R =
        nonEmpty[R]([x1, x2, y1, y2] => (evx, _) ?=> f[x1, x2])

      final def nonEmptyOut[R](f: [y1, y2] => (Y =:= (y1, y2)) ?=> R): R =
        nonEmpty[R]([x1, x2, y1, y2] => (_, evy) ?=> f[y1, y2])

      def inIsNotEmpty(using ev: X =:= EmptyTuple): Nothing =
        nonEmptyIn[Nothing] { [x1, x2] => ev1 ?=> pairIsNotEmptyTuple(using ev1.flip andThen ev) }

      def outIsNotEmpty(using ev: Y =:= EmptyTuple): Nothing =
        nonEmptyOut[Nothing] { [y1, y2] => ev1 ?=> pairIsNotEmptyTuple(using ev1.flip andThen ev) }
    }

    case class Single[X, P, I, Q, Y](
      vis: IVisualization[X, P, I, Q, Y],
    ) extends Components[Only[X], P, I, Q, Only[Y]] {
      override def ioProportions: IOProportions.ParN.Components[Only[X], Only[Y]] =
        IOProportions.ParN.Single(vis.ioProportions)

      override def size: Int = 1

      override def flexiIn:  Option[Components[Only[X], Flx, I, Q, Only[Y]]] = vis.flexiIn.map(Single(_))
      override def flexiOut: Option[Components[Only[X], P, I, Flx, Only[Y]]] = vis.flexiOut.map(Single(_))
      override def skewable: Option[Components[Only[X], P, Skw, Q, Only[Y]]] = vis.skewable.map(Single(_))

      override def trimIn: Option[Either[
        (Only[X] =:= Only[Y], EdgeDesc.TupleN.Components[Only[Y]]),
        Components[Only[X], ?, I, Q, Only[Y]]
      ]] =
        vis.trimIn.map {
          case Left((ev, d)) => Left((ev.liftCo[Only], EdgeDesc.TupleN.single(d)))
          case Right(vis)    => Right(Single(vis))
        }

      override def trimOut: Option[Either[
        (Only[X] =:= Only[Y], EdgeDesc.TupleN.Components[Only[Y]]),
        Components[Only[X], P, I, ?, Only[Y]]
      ]] =
        vis.trimOut.map {
          case Left((ev, d)) => Left((ev.liftCo[Only], EdgeDesc.TupleN.single(d)))
          case Right(vis)    => Right(Single(vis))
        }

      override def nonEmpty[R](f: [x1, x2, y1, y2] => (Only[X] =:= (x1, x2), Only[Y] =:= (y1, y2)) ?=> R): R =
        f[EmptyTuple, X, EmptyTuple, Y]
    }

    case class Snoc[X1, P, I, Q, Y1, X2, R, J, S, Y2](
      init: Components[X1, P, I, Q, Y1],
      last: IVisualization[X2, R, J, S, Y2],
    ) extends Components[
      (X1, X2),
      P | R | I | J, // input is flexible if components' inputs are flexible (P, R) and both components are skewable (I, J)
      I | J,         // skewable if both components are skewable
      Q | S | I | J, // output is flexible if components' outputs are flexible (Q, S) and both components are skewable (I, J)
      (Y1, Y2),
    ] {

      type FlI = P | R | I | J
      type FlO = Q | S | I | J
      type Sk  = I | J

      override def ioProportions: IOProportions.ParN.Components[(X1, X2), (Y1, Y2)] =
        IOProportions.ParN.Snoc(
          init.ioProportions,
          last.ioProportions,
        )

      override def size: Int = 1 + init.size

      override def flexiIn: Option[Components[(X1, X2), Flx, Sk, FlO, (Y1, Y2)]] =
        for
          a <- init.flexiIn.flatMap(_.skewable)
          b <- last.flexiIn.flatMap(_.skewable)
        yield
          Snoc(a, b)

      override def flexiOut: Option[Components[(X1, X2), FlI, Sk, Flx, (Y1, Y2)]] =
        for
          a <- init.flexiOut.flatMap(_.skewable)
          b <- last.flexiOut.flatMap(_.skewable)
        yield
          Snoc(a, b)

      override def skewable: Option[Components[ (X1, X2), FlI, Skw, FlO, (Y1, Y2)]] =
        for
          a <- init.skewable
          b <- last.skewable
        yield
          Snoc(a, b)

      override def trimIn: Option[Either[
        ((X1, X2) =:= (Y1, Y2), EdgeDesc.TupleN.Components[(Y1, Y2)]),
        Components[(X1, X2), ?, Sk, FlO, (Y1, Y2)]
      ]] =
        (init.trimIn, last.trimIn) match
          case (Some(Right(a))                 , Some(Right(b)))                  => Some(Right(Snoc(a, b)))
          case (Some(Right(a))                 , Some(Left((TypeEq(Refl()), d)))) => Some(Right(Snoc(a, Adapt(Adaptoid.Id(d)))))
          case (Some(Left((TypeEq(Refl()), c))), Some(Right(b)))                  => Some(Right(Snoc(id(c), b)))
          case (Some(Left((TypeEq(Refl()), c))), Some(Left((TypeEq(Refl()), d)))) => Some(Left((summon, EdgeDesc.TupleN.snoc(c, d))))
          case (Some(Right(a))                 , None)                            => Some(Right(Snoc(a, last)))
          case (None                           , Some(Right(b)))                  => Some(Right(Snoc(init, b)))
          case (Some(Left(_)), None) => None // cannot report as progress
          case (None, Some(Left(_))) => None // cannot report as progress
          case (None, None) => None

      override def trimOut: Option[Either[
        ((X1, X2) =:= (Y1, Y2), EdgeDesc.TupleN.Components[(Y1, Y2)]),
        Components[(X1, X2), FlI, Sk, ?, (Y1, Y2)]
      ]] =
        (init.trimOut, last.trimOut) match
          case (Some(Right(a))                 , Some(Right(b)))                  => Some(Right(Snoc(a, b)))
          case (Some(Right(a))                 , Some(Left((TypeEq(Refl()), d)))) => Some(Right(Snoc(a, Adapt(Adaptoid.Id(d)))))
          case (Some(Left((TypeEq(Refl()), c))), Some(Right(b)))                  => Some(Right(Snoc(id(c), b)))
          case (Some(Left((TypeEq(Refl()), c))), Some(Left((TypeEq(Refl()), d)))) => Some(Left((summon, EdgeDesc.TupleN.snoc(c, d))))
          case (Some(Right(a))                 , None)                            => Some(Right(Snoc(a, last)))
          case (None                           , Some(Right(b)))                  => Some(Right(Snoc(init, b)))
          case (Some(Left(_)), None) => None // cannot report as progress
          case (None, Some(Left(_))) => None // cannot report as progress
          case (None, None) => None

      override def nonEmpty[R](f: [x1, x2, y1, y2] => ((X1, X2) =:= (x1, x2), (Y1, Y2) =:= (y1, y2)) ?=> R): R =
        f[X1, X2, Y1, Y2]
    }

    def from[Wrap[_], X, Y](
      op: OpTag[Wrap],
      components: libretto.lambda.ParN[Tuple2, EmptyTuple, Visualization, X, Y],
    ): IParN[Wrap, X, ?, ?, ?, Y] =
      IParN(
        op,
        components.foldL[[x, y] =>> Components[x, ?, ?, ?, y]](
          [x, y] => vis => Single(vis.indexed),
          [x1, x2, y1, y2] => (init, last) => Snoc(init, last.indexed)
        )
      )

    def id[Wrap[_], X](desc: EdgeDesc.TupleN.Components[X]): Components[X, Flx, Skw, Flx, X] = {
      def go[X](desc: ll.TupleN[Tuple2, EmptyTuple, EdgeDesc, X]): Components[X, Flx, Skw, Flx, X] =
        desc match
          case ll.TupleN.Single(d) =>
            Single(Adapt(Adaptoid.Id(d)))
          case s: ll.TupleN.Snoc[p, n, f, x1, x2] =>
            Snoc[x1, Flx, Skw, Flx, x1, x2, Flx, Skw, Flx, x2](go(s.init), Adapt(Adaptoid.Id(s.last)))

      go(desc.unwrap)
    }
  }

  case class ConnectorsOverlay[X, J, Y](
    base: Either[IVisualization[X, Flx, J, Flx, Y], (EdgeDesc[X], EdgeDesc[Y])],
    front: List[Connector[X, Y] | TrapezoidArea[X, Y]],
  ) extends Visualization.Flexi[X, J, Y] {
    override def ioProportions: IOProportions[X, Y] =
      base match
        case Left(vis) => vis.ioProportions
        case Right((x, y)) => IOProportions.Separate(EdgeProportions.default(x), EdgeProportions.default(y))

    override def length: Length =
      base match
        case Left(vis) => Length.max(vis.length, Length.one)
        case Right(props) => Length.one

    override def skewable: Option[Visualization.Flexi[X, Skw, Y]] =
      base match
        case Left(b) =>
          b.skewable.map(b => ConnectorsOverlay(Left(b), front))
        case Right(edges) =>
          Some(ConnectorsOverlay(Right(edges), front))


    override def trimIn = None
    override def trimOut = None
  }

  case class Text[X, Y](
    value: String,
    in: EdgeDesc[X],
    out: EdgeDesc[Y],
    vpos: VPos,
  ) extends Visualization.Flexi[X, ?, Y] {
    override def length: Length = Length.one

    override def ioProportions: IOProportions[X, Y] =
      IOProportions.Separate(EdgeProportions.default(in), EdgeProportions.default(out))

    override def skewable: Option[IVisualization[X, Flx, Skw, Flx, Y]] = None

    override def trimIn = None
    override def trimOut = None
  }

  def par[∙[_, _]](using OpTag[∙]): ParBuilder[∙] =
    ParBuilder[∙]

  class ParBuilder[∙[_, _]](using op: OpTag[∙]):
    def apply[X1, X2, Y1, Y2](
      a: Visualization[X1, Y1],
      b: Visualization[X2, Y2],
    ): Visualization[X1 ∙ X2, Y1 ∙ Y2] =
      IPar(op, a.indexed, b.indexed)

  def connectors[X, Y](
    in: EdgeDesc[X],
    out: EdgeDesc[Y],
  )(
    connectors: (Connector[X, Y] | TrapezoidArea[X, Y])*
  ): Visualization.FullyFlexi[X, Y] =
    ConnectorsOverlay(
      Right((in, out)),
      connectors.toList,
    )

  def connectors[X, J, Y](
    back: Visualization.Flexi[X, J, Y],
  )(
    connectors: (Connector[X, Y] | TrapezoidArea[X, Y])*
  ): Visualization.Flexi[X, J, Y] =
    ConnectorsOverlay(
      Left(back),
      connectors.toList,
    )

  def text[X, Y](value: String)(
    iDesc: EdgeDesc[X],
    oDesc: EdgeDesc[Y],
  ): Visualization.Flexi[X, ?, Y] =
    Text(value, iDesc, oDesc, VPos.Bottom)
}
