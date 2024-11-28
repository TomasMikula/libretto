package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.NarrowCategory
import libretto.lambda.util.{Exists, TypeEq}
import libretto.lambda.util.Exists.{Some as ∃}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.examples.workflow.generic.vis.EdgeDesc.Composite

infix sealed trait IsRefinedBy[X, Y] {
  def inDesc: EdgeDesc[X]
  def outDesc: EdgeDesc[Y]
  def isStrict: Boolean

  def outDescComposite(inDesc: EdgeDesc.Composite[X]): EdgeDesc.Composite[Y]

  def asWireIdentity(using Y =:= Wire): X =:= Wire

  infix def andThen[Z](that: Y IsRefinedBy Z): X IsRefinedBy Z

  infix def par[∙[_, _], V, W](that: V IsRefinedBy W)(using op: OpTag[∙]): (X ∙ V) IsRefinedBy (Y ∙ W) =
    IsRefinedBy.par(this, that)

  /** Returns the most refined `V` such that `V` is a coarsening of both `X` and `W`. */
  infix def greatestCommonCoarsening[W](
    that: W IsRefinedBy Y,
  ): Exists[[V] =>> (
    V IsRefinedBy X,
    V IsRefinedBy W,
  )]

  /** Two (potentially different) coarsenings of `Y` can be morphed into each other. */
  infix def morph[W](that: W IsRefinedBy Y): Adaptoid[X, W]
}

object IsRefinedBy {
  case class Id[X](desc: EdgeDesc[X]) extends IsRefinedBy[X, X] {
    override def inDesc: EdgeDesc[X] =
      desc

    override def outDesc: EdgeDesc[X] =
      desc

    override def isStrict: Boolean =
      false

    override def outDescComposite(inDesc: EdgeDesc.Composite[X]): EdgeDesc.Composite[X] =
      inDesc

    override def asWireIdentity(using X =:= Wire): X =:= Wire =
      summon

    override def andThen[Z](that: X IsRefinedBy Z): X IsRefinedBy Z =
      that

    override def greatestCommonCoarsening[W](
      that: W IsRefinedBy X,
    ): Exists[[V] =>> (V IsRefinedBy X, V IsRefinedBy W)] =
      Exists((that, Id[W](that.inDesc)))

    override def morph[W](that: W IsRefinedBy X): Adaptoid[X, W] =
      Adaptoid.collapse(that)
  }

  infix sealed trait IsStrictlyRefinedBy[X, Y] extends IsRefinedBy[X, Y] {
    override def isStrict: Boolean = true
  }

  case class Initial[X](outDesc: EdgeDesc.Composite[X]) extends (Wire IsStrictlyRefinedBy X) {
    override def inDesc: EdgeDesc[Wire] = EdgeDesc.SingleWire

    override def outDescComposite(
      inDesc: EdgeDesc.Composite[Wire] // impossible input
    ): EdgeDesc.Composite[X] =
      outDesc

    override def asWireIdentity(using
      X =:= Wire, // impossible input
    ): Wire =:= Wire =
      summon

    override def andThen[Z](that: X IsRefinedBy Z): Wire IsRefinedBy Z =
      Initial(that.outDescComposite(this.outDesc))

    override def greatestCommonCoarsening[W](
      that: W IsRefinedBy X,
    ): Exists[[V] =>> (V IsRefinedBy Wire, V IsRefinedBy W)] =
      Exists((id[Wire], initial[W](that.inDesc)))

    override def morph[W](that: W IsRefinedBy X): Adaptoid[Wire, W] =
      Adaptoid.expand(initial[W](that.inDesc))
  }

  case class Pairwise[∙[_, _], X1, X2, Y1, Y2](
    op: OpTag[∙],
    f1: X1 IsRefinedBy Y1,
    f2: X2 IsRefinedBy Y2,
  ) extends IsStrictlyRefinedBy[X1 ∙ X2, Y1 ∙ Y2] {
    require(
      (f1, f2) match {
        case (Id(_), Id(_)) => false
        case _ => true
      },
      "The sides of Pairwise cannot both be Id"
    )

    private given OpTag[∙] = op

    override def inDesc: EdgeDesc[X1 ∙ X2] =
      EdgeDesc.binary(f1.inDesc, f2.inDesc)

    override def outDesc: EdgeDesc[Y1 ∙ Y2] =
      EdgeDesc.binary(f1.outDesc, f2.outDesc)

    override def outDescComposite(inDesc: EdgeDesc.Composite[X1 ∙ X2]): EdgeDesc.Composite[Y1 ∙ Y2] =
      EdgeDesc.binary(f1.outDesc, f2.outDesc)

    override def asWireIdentity(using ev: (Y1 ∙ Y2) =:= Wire): (X1 ∙ X2) =:= Wire =
      Wire.isNotBinary[∙, Y1, Y2](using ev.flip)

    override def andThen[Z](that: (Y1 ∙ Y2) IsRefinedBy Z): (X1 ∙ X2) IsRefinedBy Z =
      that match
        case Pairwise(op_, g1, g2) => Pairwise(op, f1 andThen g1, f2 andThen g2)
        case Id(desc) => this
        case Initial(outDesc) => throw AssertionError("Impossible Wire =:= (X1 ∙ X2) if `∙` is a class type different from Wire")

    override def greatestCommonCoarsening[W](
      that: W IsRefinedBy (Y1 ∙ Y2),
    ): Exists[[V] =>> (V IsRefinedBy (X1 ∙ X2), V IsRefinedBy W)] =
      that match
        case Id(_) => Exists((Id(inDesc), this))
        case Initial(_) => Exists((initial(inDesc), id[Wire]))
        case Pairwise(_, g1, g2) => greatestCommonCoarseningPairwise(g1, g2)

    private def greatestCommonCoarseningPairwise[W1, W2](
      g1: W1 IsRefinedBy Y1,
      g2: W2 IsRefinedBy Y2,
    ): Exists[[V] =>> (V IsRefinedBy (X1 ∙ X2), V IsRefinedBy (W1 ∙ W2))] =
      (f1 greatestCommonCoarsening g1, f2 greatestCommonCoarsening g2) match
        case (∃((wf1, wg1)), ∃((wf2, wg2))) =>
          Exists((Pairwise(op, wf1, wf2), Pairwise(op, wg1, wg2)))

    override def morph[W](
      that: W IsRefinedBy (Y1 ∙ Y2),
    ): Adaptoid[(X1 ∙ X2), W] =
      that match
        case Id(_) => Adaptoid.Expand(this)
        case Initial(_) => Adaptoid.collapse(initial(inDesc))
        case Pairwise(_, g1, g2) => morphToBinaryOp(g1, g2)

    private def morphToBinaryOp[W1, W2](
      g1: W1 IsRefinedBy Y1,
      g2: W2 IsRefinedBy Y2,
    ): Adaptoid[X1 ∙ X2, W1 ∙ W2] =
      Adaptoid.par(using op)(f1 morph g1, f2 morph g2)
  }

  case class ParN[Wrap[_], X, Y](
    op: OpTag[Wrap],
    components: ParN.Components[X, Y],
  ) extends (Wrap[X] IsStrictlyRefinedBy Wrap[Y]) {
    require(
      components.exists([x, y] => _.isStrict),
      "At least 1 component of IsRefinedBy.ParN must be *strictly* refining"
    )

    override def morph[W](that: W IsRefinedBy Wrap[Y]): Adaptoid[Wrap[X], W] = ???

    override def greatestCommonCoarsening[W](that: W IsRefinedBy Wrap[Y]): Exists[[V] =>> (V IsRefinedBy Wrap[X], V IsRefinedBy W)] = ???

    override def inDesc: EdgeDesc[Wrap[X]] = ???

    override def outDescComposite(inDesc: Composite[Wrap[X]]): Composite[Wrap[Y]] = ???

    override def outDesc: EdgeDesc[Wrap[Y]] = ???

    override def andThen[Z](that: Wrap[Y] IsRefinedBy Z): Wrap[X] IsRefinedBy Z = ???

    override def asWireIdentity(using ev: Wrap[Y] =:= Wire): Wrap[X] =:= Wire =
      Wire.isNotUnary[Wrap, Y](using ev.flip)

  }

  object ParN {
    type Components[X, Y] = libretto.lambda.ParN[Tuple2, EmptyTuple, IsRefinedBy, X, Y]
  }

  def id[X](using EdgeDesc[X]): (X IsRefinedBy X) =
    Id[X](summon)

  def initial[X](x: EdgeDesc[X]): (Wire IsRefinedBy X) =
    x match
      case w @ EdgeDesc.SingleWire  => Id(w)
      case c: EdgeDesc.Composite[X] => Initial[X](c)

  def par[∙[_, _], X1, X2, Y1, Y2](
    f1: X1 IsRefinedBy Y1,
    f2: X2 IsRefinedBy Y2,
  )(using
    op: OpTag[∙],
  ): (X1 ∙ X2) IsRefinedBy (Y1 ∙ Y2) =
    (f1, f2) match
      case (Id(x1), Id(x2)) => Id(x1 ∙ x2)
      case _                => Pairwise(op, f1, f2)

  def parN[Wrap[_], X, Y](
    op: OpTag[Wrap],
    components: ParN.Components[X, Y],
  ): (Wrap[X] IsRefinedBy Wrap[Y]) =
    allIdentities(components) match
      case Some(TypeEq(Refl())) =>
        Id(EdgeDesc.TupleN.make(op, components.inputProjection([x, y] => f => f.inDesc)))
      case None =>
        ParN(op, components)

  private def allIdentities[X, Y](
    components: ParN.Components[X, Y],
  ): Option[X =:= Y] =
    components match
      case libretto.lambda.ParN.Single(f) =>
        f match
          case IsRefinedBy.Id(_) => Some(summon[X =:= Y])
          case _                 => None
      case libretto.lambda.ParN.Snoc(init, last) =>
        last match
          case IsRefinedBy.Id(_) =>
            allIdentities(init)
              .map { case ev @ TypeEq(Refl()) => summon[X =:= Y] }
          case _ =>
            None

  def wireIsBottom[X](f: X IsRefinedBy Wire): (X =:= Wire) =
    f.asWireIdentity

  def anythingRefinesWire[X](using EdgeDesc[X]): (Wire IsRefinedBy X) =
    initial[X](summon)

  given NarrowCategory[IsRefinedBy, EdgeDesc] with {
    override def andThen[A, B, C](f: A IsRefinedBy B, g: B IsRefinedBy C): A IsRefinedBy C =
      f andThen g

    override def id[A](witness: EdgeDesc[A]): A IsRefinedBy A =
      Id(witness)
  }
}
