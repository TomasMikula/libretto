package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.lang.{**, ++}
import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.{Some as ∃}

infix sealed trait Approximates[X, A] {
  import Approximates.*

  def inDesc: EdgeDesc[X]

  infix def pair[Y, B](that: Approximates[Y, B]): Approximates[X ** Y, A ** B] =
    Pairwise(this, that)

  def ++[Y, B](that: Approximates[Y, B]): Approximates[X ++ Y, A ++ B] =
    Pairwise(this, that)

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

  infix def leastCommonRefinement[Y](that: Y Approximates A): Exists[[Z] =>> (Z Approximates A, X IsRefinedBy Z, Y IsRefinedBy Z)]
}

object Approximates {
  case class Initial[A]() extends Approximates[Wire, A] {
    override def inDesc: EdgeDesc[Wire] =
      EdgeDesc.SingleWire

    override def leastCommonRefinement[Y](that: Y Approximates A): Exists[[Z] =>> (Z Approximates A, Wire IsRefinedBy Z, Y IsRefinedBy Z)] =
      Exists((that, IsRefinedBy.Initial[Y](that.inDesc), IsRefinedBy.Id[Y](that.inDesc)))

    override protected def coarsenByPair[∙[_, _], W1, W2, X1, X2](
      g1: W1 IsRefinedBy X1,
      g2: W2 IsRefinedBy X2,
    )(using
      ev: Wire =:= (X1 ∙ X2),
    ): (W1 ∙ W2) Approximates A =
      ???
  }

  case class Pairwise[∙[_, _], X1, X2, A1, A2](
    f1: X1 Approximates A1,
    f2: X2 Approximates A2,
  ) extends Approximates[X1 ∙ X2, A1 ∙ A2] {
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
          Exists((this, IsRefinedBy.Id[X1 ∙ X2](inDesc), IsRefinedBy.Initial[X1 ∙ X2](inDesc)))
        case Pairwise(f1, f2) =>
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
          Exists((Pairwise(z1, z2), zf1 pair zf2, zg1 pair zg2))

    override protected def coarsenByPair[∘[_, _], W1, W2, Y1, Y2](
      g1: W1 IsRefinedBy Y1,
      g2: W2 IsRefinedBy Y2,
    )(using
      (X1 ∙ X2) =:= (Y1 ∘ Y2),
    ): (W1 ∘ W2) Approximates (A1 ∙ A2) =
      ???
  }

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
          IsRefinedBy.Initial(EdgeDesc.binary(EdgeDesc.wire, EdgeDesc.wire))
        )))
      case Pairwise(f1, f2) =>
        Exists(Exists((f1, f2, IsRefinedBy.Id(f.inDesc))))

}
