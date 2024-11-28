package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.lang.{++, **}

import DefaultDimensions.Length

sealed trait EdgeDesc[X] {
  def depth: Length

  def combine[∙[_, _]](using OpTag[∙]): BinaryBuilder[∙] =
    BinaryBuilder[∙]

  class BinaryBuilder[∙[_, _]](using op: OpTag[∙]) {
    def apply[Y](that: EdgeDesc[Y]): EdgeDesc[X ∙ Y] =
      EdgeDesc.this ∙ that
  }

  def ∙[∙[_, _], Y](that: EdgeDesc[Y])(using OpTag[∙]): EdgeDesc[X ∙ Y] =
    EdgeDesc.Binary[∙, X, Y](summon, this, that)

  def ++[Y](that: EdgeDesc[Y]): EdgeDesc[X ++ Y] =
    this ∙ that

  def **[Y](that: EdgeDesc[Y]): EdgeDesc[X ** Y] =
    this ∙ that

  def isComposite: Either[X =:= Wire, EdgeDesc.Composite[X]]
}

object EdgeDesc {
  case object SingleWire extends EdgeDesc[Wire] {
    override def depth: Length =
      Length.one

    override def isComposite: Either[Wire =:= Wire, Composite[Wire]] =
      Left(summon)
  }

  sealed trait Composite[X] extends EdgeDesc[X] {
    override def isComposite: Either[X =:= Wire, Composite[X]] =
      Right(this)
  }

  case class Binary[∙[_, _], X1, X2](
    op: OpTag[∙],
    x1: EdgeDesc[X1],
    x2: EdgeDesc[X2],
  ) extends EdgeDesc.Composite[X1 ∙ X2]:
    override def depth: Length =
      (x1, x2) match
        case (SingleWire, SingleWire) =>
          Length.one
        case _ =>
          Length.cram(
            Length.one,
            Length.max(x1.depth, x2.depth)
          )

  case class TupleN[Wrap[_], X](
    op: OpTag[Wrap],
    components: TupleN.Components[X],
  ) extends Composite[Wrap[X]] {
    override def depth: Length =
      Length.cram(
        Length.one,
        components.depth
      )
  }

  object TupleN {
    opaque type Components[X] = libretto.lambda.TupleN[Tuple2, EmptyTuple, EdgeDesc, X]

    extension [X](comps: Components[X]) {
      def unwrap: libretto.lambda.TupleN[Tuple2, EmptyTuple, EdgeDesc, X] =
        comps

      def depth: Length =
        comps match
          case libretto.lambda.TupleN.Single(x) => x.depth
          case libretto.lambda.TupleN.Snoc(init, last) => Length.max(init.depth, last.depth)
    }

    def single[X](value: EdgeDesc[X]): Components[Only[X]] =
      libretto.lambda.TupleN.Single(value)

    def snoc[X1, X2](
      init: Components[X1],
      last: EdgeDesc[X2],
    ): Components[(X1, X2)] =
      libretto.lambda.TupleN.Snoc(init, last)

    def make[Wrap[_], X](
      op: OpTag[Wrap],
      components: libretto.lambda.TupleN[Tuple2, EmptyTuple, EdgeDesc, X],
    ): Composite[Wrap[X]] =
      TupleN(op, components)
  }

  given wire: EdgeDesc[Wire] =
    SingleWire

  def binary[∙[_, _], X1, X2](using
    op: OpTag[∙],
  )(
    x1: EdgeDesc[X1],
    x2: EdgeDesc[X2],
  ): EdgeDesc.Composite[X1 ∙ X2] =
    Binary(op, x1, x2)
}
