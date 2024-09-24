package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.{Some as ∃}

infix sealed trait IsRefinedBy[X, Y] {
  def inDesc: EdgeDesc[X]

  infix def pair[∙[_, _], V, W](that: V IsRefinedBy W): (X ∙ V) IsRefinedBy (Y ∙ W) =
    IsRefinedBy.Pairwise(this, that)

  /** Returns the most refined `V` such that `V` is a coarsening of both `X` and `W`. */
  infix def greatestCommonCoarsening[W](
    that: W IsRefinedBy Y,
  ): Exists[[V] =>> (
    V IsRefinedBy X,
    V IsRefinedBy W,
  )]

  /** Two (potentially different) coarsenings of `Y` can be morphed into each other. */
  infix def morph[W](that: W IsRefinedBy Y): Morph[X, W]
}

object IsRefinedBy {
  case class Id[X](desc: EdgeDesc[X]) extends IsRefinedBy[X, X] {
    override def inDesc: EdgeDesc[X] =
      desc

    override def greatestCommonCoarsening[W](
      that: W IsRefinedBy X,
    ): Exists[[V] =>> (V IsRefinedBy X, V IsRefinedBy W)] =
      Exists((that, Id[W](that.inDesc)))

    override def morph[W](that: W IsRefinedBy X): Morph[X, W] =
      Morph.Unrefine(that)
  }

  case class Initial[X](outDesc: EdgeDesc[X]) extends (Wire IsRefinedBy X) {
    override def inDesc: EdgeDesc[Wire] = EdgeDesc.SingleWire

    override def greatestCommonCoarsening[W](
      that: W IsRefinedBy X,
    ): Exists[[V] =>> (V IsRefinedBy Wire, V IsRefinedBy W)] =
      Exists((id[Wire], Initial[W](that.inDesc)))

    override def morph[W](that: W IsRefinedBy X): Morph[Wire, W] =
      Morph.Refine(Initial[W](that.inDesc))
  }

  case class Pairwise[∙[_, _], X1, X2, Y1, Y2](
    f1: X1 IsRefinedBy Y1,
    f2: X2 IsRefinedBy Y2,
  ) extends IsRefinedBy[X1 ∙ X2, Y1 ∙ Y2] {
    override def inDesc: EdgeDesc[(X1 ∙ X2)] =
      EdgeDesc.binary(f1.inDesc, f2.inDesc)

    override def greatestCommonCoarsening[W](
      that: W IsRefinedBy (Y1 ∙ Y2),
    ): Exists[[V] =>> (V IsRefinedBy (X1 ∙ X2), V IsRefinedBy W)] =
      that match
        case Id(_) => Exists((Id(inDesc), this))
        case Initial(_) => Exists((Initial(inDesc), id[Wire]))
        case Pairwise(g1, g2) => greatestCommonCoarseningPairwise(g1, g2)

    private def greatestCommonCoarseningPairwise[W1, W2](
      g1: W1 IsRefinedBy Y1,
      g2: W2 IsRefinedBy Y2,
    ): Exists[[V] =>> (V IsRefinedBy (X1 ∙ X2), V IsRefinedBy (W1 ∙ W2))] =
      (f1 greatestCommonCoarsening g1, f2 greatestCommonCoarsening g2) match
        case (∃((wf1, wg1)), ∃((wf2, wg2))) =>
          Exists((Pairwise(wf1, wf2), Pairwise(wg1, wg2)))

    override def morph[W](
      that: W IsRefinedBy (Y1 ∙ Y2),
    ): Morph[(X1 ∙ X2), W] =
      that match
        case Id(_) => Morph.Refine(this)
        case Initial(_) => Morph.Unrefine(Initial(inDesc))
        case Pairwise(g1, g2) => morphToBinaryOp(g1, g2)

    private def morphToBinaryOp[W1, W2](
      g1: W1 IsRefinedBy Y1,
      g2: W2 IsRefinedBy Y2,
    ): Morph[X1 ∙ X2, W1 ∙ W2] =
      Morph.par(f1 morph g1, f2 morph g2)
  }

  def id[X](using EdgeDesc[X]): (X IsRefinedBy X) =
    Id[X](summon)

  def anythingRefinesWire[X](using EdgeDesc[X]): (Wire IsRefinedBy X) =
    Initial[X](summon)
}
