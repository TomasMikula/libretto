package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.{DropNames, ParN}
import libretto.lambda.examples.workflow.generic.lang.{**, ++, ||, ::}
import libretto.lambda.util.{Exists, Functional, TypeEq}
import libretto.lambda.util.Exists.{Some as ∃}
import libretto.lambda.util.TypeEq.Refl

infix sealed trait Approximates[X, A] {
  import Approximates.*

  def inDesc: EdgeDesc[X]

  def **[Y, B](that: Approximates[Y, B]): Approximates[X ** Y, A ** B] =
    Pairwise(summon, this, that)

  def ++[Y, B](that: Approximates[Y, B]): Approximates[X ++ Y, A ++ B] =
    Pairwise(summon, this, that)

  infix def coarsenBy[W](that: W IsRefinedBy X): W Approximates A =
    import IsRefinedBy as R
    that match
      case R.Id(_) => this
      case R.Initial(_) => Initial()
      case p: R.Pairwise[op, w1, w2, x1, x2] => coarsenByPair[op, w1, w2, x1, x2](p.f1, p.f2)

  protected def coarsenByPair[∙[_, _], W1, W2, X1, X2](
    g1: W1 IsRefinedBy X1,
    g2: W2 IsRefinedBy X2,
  )(using
    X =:= (X1 ∙ X2),
  ): (W1 ∙ W2) Approximates A

  infix def leastCommonRefinement[Y](
    that: Y Approximates A,
  ): Exists[[Z] =>> (
    Z Approximates A,
    X IsRefinedBy Z,
    Y IsRefinedBy Z
  )]

  infix def greatestCommonCoarsening[Y](
    that: Y Approximates A,
  ): Exists[[W] =>> (
    W IsRefinedBy X,
    W IsRefinedBy Y,
    W Approximates A,
  )]
}

object Approximates {
  case class Initial[A]() extends Approximates[Wire, A] {
    override def inDesc: EdgeDesc[Wire] =
      EdgeDesc.SingleWire

    override def leastCommonRefinement[Y](
      that: Y Approximates A
    ): Exists[[Z] =>> (Z Approximates A, Wire IsRefinedBy Z, Y IsRefinedBy Z)] =
      Exists((that, IsRefinedBy.initial[Y](that.inDesc), IsRefinedBy.Id[Y](that.inDesc)))

    override def greatestCommonCoarsening[Y](
      that: Y Approximates A,
    ): Exists[[W] =>> (W IsRefinedBy Wire, W IsRefinedBy Y, W Approximates A)] =
      Exists((IsRefinedBy.id[Wire], IsRefinedBy.initial[Y](that.inDesc), this))

    override protected def coarsenByPair[∙[_, _], W1, W2, X1, X2](
      g1: W1 IsRefinedBy X1,
      g2: W2 IsRefinedBy X2,
    )(using
      ev: Wire =:= (X1 ∙ X2),
    ): (W1 ∙ W2) Approximates A =
      ???
  }

  case class Pairwise[∙[_, _], X1, X2, A1, A2](
    op: OpTag[∙],
    f1: X1 Approximates A1,
    f2: X2 Approximates A2,
  ) extends Approximates[X1 ∙ X2, A1 ∙ A2] {
    private given OpTag[∙] = op

    override def inDesc: EdgeDesc[X1 ∙ X2] =
      EdgeDesc.binary(f1.inDesc, f2.inDesc)

    override def leastCommonRefinement[Y](
      that: Y Approximates (A1 ∙ A2),
    ): Exists[[Z] =>> (
      Z Approximates (A1 ∙ A2),
      (X1 ∙ X2) IsRefinedBy Z,
      Y IsRefinedBy Z,
    )] =
      that match
        case Initial() =>
          summon[Y =:= Wire]
          Exists((this, IsRefinedBy.Id[X1 ∙ X2](inDesc), IsRefinedBy.initial[X1 ∙ X2](inDesc)))
        case Pairwise(_, f1, f2) =>
          leastCommonRefinementPairwise(f1, f2)

    private def leastCommonRefinementPairwise[Y1, Y2](
      g1: Y1 Approximates A1,
      g2: Y2 Approximates A2,
    ): Exists[[Z] =>> (
      Z Approximates (A1 ∙ A2),
      (X1 ∙ X2) IsRefinedBy Z,
      (Y1 ∙ Y2) IsRefinedBy Z,
    )] =
      (f1 leastCommonRefinement g1, f2 leastCommonRefinement g2) match
        case (∃((z1, zf1, zg1)), ∃((z2, zf2, zg2))) =>
          Exists((Pairwise(op, z1, z2), zf1 par zf2, zg1 par zg2))

    override def greatestCommonCoarsening[Y](
      that: Y Approximates (A1 ∙ A2),
    ): Exists[[W] =>> (
      W IsRefinedBy (X1 ∙ X2),
      W IsRefinedBy Y,
      W Approximates (A1 ∙ A2),
    )] = ???

    override protected def coarsenByPair[∘[_, _], W1, W2, Y1, Y2](
      g1: W1 IsRefinedBy Y1,
      g2: W2 IsRefinedBy Y2,
    )(using
      (X1 ∙ X2) =:= (Y1 ∘ Y2),
    ): (W1 ∘ W2) Approximates (A1 ∙ A2) =
      ???
  }

  case class ParNDropNames[Wrap[_], X, A0, A](
    op: OpTag[Wrap],
    dropNames: DropNames[||, ::, Tuple2, EmptyTuple, A, A0],
    components: ParN[Tuple2, EmptyTuple, Approximates, X, A0]
  ) extends Approximates[Wrap[X], Wrap[A]] {

    override def inDesc: EdgeDesc[Wrap[X]] =
      EdgeDesc.TupleN.make(
        op,
        components.inputProjection[EdgeDesc]([x, y] => _.inDesc),
      )

    override protected def coarsenByPair[∙[_$1,_$2], W1, W2, X1, X2](g1: W1 IsRefinedBy X1, g2: W2 IsRefinedBy X2)(using Wrap[X] =:= ∙[X1, X2]): ∙[W1, W2] Approximates Wrap[A] = ???

    override def leastCommonRefinement[Y](
      that: Y Approximates Wrap[A],
    ): Exists[[Z] =>> (
      Z Approximates Wrap[A],
      Wrap[X] IsRefinedBy Z,
      Y IsRefinedBy Z,
    )] =
      that match
        case Initial() =>
          Exists((
            this,
            IsRefinedBy.id[Wrap[X]](using inDesc),
            IsRefinedBy.initial(inDesc)
          ))
        case ParNDropNames(op1, dropNames1, components1) =>
          summon[Functional[DropNames[||, ::, Tuple2, EmptyTuple, _, _]]]
            .uniqueOutputType(dropNames, dropNames1) match
              case TypeEq(Refl()) =>
                leastCommonRefinementElementWise(components, components1) match
                  case Exists.Some((zs, xs, ys)) =>
                    Exists((
                      ParNDropNames(op, dropNames, zs),
                      IsRefinedBy.parN(op, xs),
                      IsRefinedBy.parN(op, ys)
                    ))
        case Pairwise(op, f1, f2) =>
          throw AssertionError("Impossible if `Wrap` and `∙` are distinct class types")

    private def leastCommonRefinementElementWise[Xs, Ys, As](
      xs: ParN[Tuple2, EmptyTuple, Approximates, Xs, As],
      ys: ParN[Tuple2, EmptyTuple, Approximates, Ys, As],
    ): Exists[[Zs] =>> (
      ParN[Tuple2, EmptyTuple, Approximates, Zs, As],
      ParN[Tuple2, EmptyTuple, IsRefinedBy, Xs, Zs],
      ParN[Tuple2, EmptyTuple, IsRefinedBy, Ys, Zs],
    )] =
      (xs, ys) match
        case (ParN.Single(x), ParN.Single(y)) =>
          (x leastCommonRefinement y) match
            case Exists.Some((za, xz, yz)) =>
              Exists((ParN.Single(za), ParN.Single(xz), ParN.Single(yz)))
        case (ParN.Snoc(xs, x), ParN.Snoc(ys, y)) =>
          (leastCommonRefinementElementWise(xs, ys), x leastCommonRefinement y) match
            case (Exists.Some((zas, xzs, yzs)), Exists.Some((za, xz, yz))) =>
              Exists((ParN.Snoc(zas, za), ParN.Snoc(xzs, xz), ParN.Snoc(yzs, yz)))

    override def greatestCommonCoarsening[Y](
      that: Y Approximates Wrap[A],
    ): Exists[[W] =>> (
      W IsRefinedBy Wrap[X],
      W IsRefinedBy Y,
      W Approximates Wrap[A],
    )] =
      that match
        case Initial() =>
          Exists((
            IsRefinedBy.initial(this.inDesc),
            IsRefinedBy.initial(that.inDesc),
            Initial()
          ))
        case ParNDropNames(op1, dropNames1, components1) =>
          summon[Functional[DropNames[||, ::, Tuple2, EmptyTuple, _, _]]]
            .uniqueOutputType(dropNames, dropNames1) match
              case TypeEq(Refl()) =>
                greatestCommonCoarseningElementWise(components, components1) match
                  case Exists.Some((xs, ys, as)) =>
                    Exists((
                      IsRefinedBy.parN(op, xs),
                      IsRefinedBy.parN(op, ys),
                      ParNDropNames(op, dropNames, as),
                    ))
        case Pairwise(op, f1, f2) =>
          throw AssertionError("Impossible if `Wrap` and `∙` are distinct class types")

    private def greatestCommonCoarseningElementWise[Xs, Ys, As](
      xs: ParN[Tuple2, EmptyTuple, Approximates, Xs, As],
      ys: ParN[Tuple2, EmptyTuple, Approximates, Ys, As],
    ): Exists[[Ws] =>> (
      ParN[Tuple2, EmptyTuple, IsRefinedBy, Ws, Xs],
      ParN[Tuple2, EmptyTuple, IsRefinedBy, Ws, Ys],
      ParN[Tuple2, EmptyTuple, Approximates, Ws, As],
    )] =
      (xs, ys) match
        case (ParN.Single(x), ParN.Single(y)) =>
          (x greatestCommonCoarsening y) match
            case Exists.Some((wx, wy, wa)) =>
              Exists((ParN.Single(wx), ParN.Single(wy), ParN.Single(wa)))
        case (ParN.Snoc(xs, x), ParN.Snoc(ys, y)) =>
          (greatestCommonCoarseningElementWise(xs, ys), x greatestCommonCoarsening y) match
            case (Exists.Some((wxs, wys, was)), Exists.Some((wx, wy, wa))) =>
              Exists((ParN.Snoc(wxs, wx), ParN.Snoc(wys, wy), ParN.Snoc(was, wa)))
  }

  def lump[A]: Wire Approximates A =
    Initial()

  given Approximation[Approximates] with {
    override def lump[A] =
      Initial[A]()

    extension [X, A](x: X Approximates A)
      override infix def unify[Y](
        y: Y Approximates A,
      ): Exists[[Z] =>> (Z Approximates A, X IsRefinedBy Z, Y IsRefinedBy Z)] =
        x leastCommonRefinement y

  }

  def unplus[X, A, B](f: X Approximates (A ++ B)): Exists[[Xa] =>> Exists[[Xb] =>> (
    Xa Approximates A,
    Xb Approximates B,
    X IsRefinedBy (Xa ++ Xb),
  )]] =
    f match
      case Initial() =>
        Exists(Exists((
          Initial[A](),
          Initial[B](),
          IsRefinedBy.initial(EdgeDesc.binary(using summon[OpTag[++]])(EdgeDesc.wire, EdgeDesc.wire))
        )))
      case Pairwise(_, f1, f2) =>
        Exists(Exists((f1, f2, IsRefinedBy.Id(f.inDesc))))

}
