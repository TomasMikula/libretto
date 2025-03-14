package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.{DistributionNAry, DropNames, ParN, SinkNAryNamed, SinkNAry, TupleElem}
import libretto.lambda.examples.workflow.generic.lang.{++, **, ::, ||, Enum, FlowAST, Workflows}
import libretto.lambda.util.{Exists, TypeEq}
import libretto.lambda.util.Exists.{Some as ∃}
import libretto.lambda.util.TypeEq.Refl

import Approximates.lump
import Connector.{Across, StudIn, StudOut}
import DefaultDimensions.Length
import EdgeDesc.wire
import IOProportions.EdgeProportions
import PredefinedFill.{GradientVerticalWhiteBlack, VerticalFadeOutLeft, VerticalFadeOutRight}
import StyleDefs.{ColorCaseLeft, ColorCaseRight}
import Visualization.{Flx, IVisualization, Skw}
import WirePick.{pickId, pickL, pickR}

object FlowVisualizer {
  def apply[Op[_, _]](using
    workflows: Workflows[Op],
    visOp: Visualizer[Op, Approximates],
  ): FlowVisualizer[Op, workflows.Flow] =
    new FlowVisualizer[Op, workflows.Flow]
}

class FlowVisualizer[Op[_, _], F[_, _]](using
  val workflows: Workflows[Op] { type Flow[A, B] = F[A, B] },
  visOp: Visualizer[Op, Approximates],
) extends Visualizer[F, Approximates] {
  import FlowVisualizer.*

  extension [A, B](f: F[A, B])
    override def visualize =
      visualizeAst(f.ast)

  private def visualizeAst[A, B](f: FlowAST[Op, A, B]): Exists[[X] =>> Exists[[Y] =>> (
    X Approximates A,
    Y Approximates B,
    Visualization[X, Y],
  )]] = {
    f match
      case FlowAST.Ext(action) =>
        action.visualize

      case FlowAST.AndThen(g, h) =>
        (visualizeAst(g), visualizeAst(h)) match
          case (∃(∃((x, y1, vg))), ∃(∃((y2, z, vh)))) =>
            val m = y1 adaptTo y2
            Exists(Exists((x, z, Visualization.Sequence(vg, Visualization.Adapt(m), vh))))

      case FlowAST.Par(g, h) =>
        (visualizeAst(g), visualizeAst(h)) match
          case (∃(∃((x1, y1, vg))), ∃(∃((x2, y2, vh)))) =>
            Exists(Exists((x1 ** x2, y1 ** y2, Visualization.par[**](vg, vh))))

      case FlowAST.Handle(handlers) =>
        visualizeHandlers(handlers)

      case FlowAST.DoWhile(g) =>
        visualizeAst(g) match
          case ∃(∃((x, xy, vg))) =>
            Exists(Exists((
              lump[A],
              lump[B],
              Visualization.Sequence(
                Visualization.connectors(
                  wire,
                  wire ** wire,
                )(
                  Connector.Across(pickId, pickR),
                  Connector.LoopOut(pickL, pickR),
                ),
                Visualization.par[**](
                  Visualization.connectors(wire, wire)(Connector.Across(pickId, pickId)),
                  Visualization.Sequence(
                    Visualization.Adapt(lump[A] adaptTo x),
                    vg,
                    Visualization.Adapt(xy adaptTo (lump[A] ++ lump[B])),
                  ),
                ),
                Visualization.connectors(
                  wire ** (wire ++ wire),
                  wire,
                )(
                  Connector.Across(pickR[++, Wire].inr, pickId),
                  Connector.LoopIn(pickL[++, Wire].inr, pickL),
                ),
              )
            )))

      case FlowAST.Id() =>
        summon[A =:= B]
        Exists(Exists((
          lump[A],
          lump[B],
          Visualization.connectors(
            wire,
            wire,
          )(
            Across(pickId, pickId),
          )
        )))

      case _: FlowAST.Swap[op, x, y] =>
        summon[A =:= (x ** y)]
        summon[B =:= (y ** x)]
        Exists(Exists((
          lump[x] ** lump[y],
          lump[y] ** lump[x],
          Visualization.connectors(
            wire ** wire,
            wire ** wire,
          )(
            Across(pickL, pickR),
            Across(pickR, pickL),
          )
        )))

      case _: FlowAST.AssocLR[op, x, y, z] =>
        summon[A =:= ((x ** y) ** z)]
        summon[B =:= (x ** (y ** z))]

        Exists(Exists((
          (lump[x] ** lump[y]) ** lump[z],
          lump[x] ** (lump[y] ** lump[z]),
          Visualization.connectors(
            (wire ** wire) ** wire,
            wire ** (wire ** wire),
          )(
            Across(pickL.inl, pickL),
            Across(pickR.inl, pickL.inr),
            Across(pickR, pickR.inr),
          )
        )))

      case _: FlowAST.AssocRL[op, x, y, z] =>
        summon[A =:= (x ** (y ** z))]
        summon[B =:= ((x ** y) ** z)]

        Exists(Exists((
          lump[x] ** (lump[y] ** lump[z]),
          (lump[x] ** lump[y]) ** lump[z],
          Visualization.connectors(
            wire ** (wire ** wire),
            (wire ** wire) ** wire,
          )(
            Across(pickL, pickL.inl),
            Across(pickL.inr, pickR.inl),
            Across(pickR.inr, pickR),
          )
        )))

      case _: FlowAST.Prj1[op, x, y] =>
        summon[A =:= (x ** y)]
        summon[B =:= x]

        Exists(Exists((
          lump[x] ** lump[y],
          lump[x],
          Visualization.connectors(
            wire ** wire,
            wire,
          )(
            Across(pickL, pickId),
            StudIn(pickR),
          )
        )))

      case _: FlowAST.Prj2[op, x, y] =>
        summon[A =:= (x ** y)]
        summon[B =:= y]

        Exists(Exists((
          lump[x] ** lump[y],
          lump[y],
          Visualization.connectors(
            wire ** wire,
            wire,
          )(
            Across(pickR, pickId),
            StudIn(pickL),
          )
        )))

      case _: FlowAST.IntroFst[op, x] =>
        summon[A =:= x]
        summon[B =:= (Unit ** x)]

        Exists(Exists((
          lump[x],
          lump[Unit] ** lump[x],
          Visualization.connectors(
            wire,
            wire ** wire,
          )(
            Across(pickId, pickR),
            StudOut(pickL),
          )
        )))

      case _: FlowAST.Dup[op, x] =>
        summon[A =:= x]
        summon[B =:= (x ** x)]

        Exists(Exists((
          lump[x],
          lump[x] ** lump[x],
          Visualization.connectors(
            back = Visualization.text("Δ")(
              wire,
              wire ** wire,
            )
          )(
            Across(pickId, pickL),
            Across(pickId, pickR),
          )
        )))

      case d: FlowAST.DistributeNAryLR[op, d, cases, dCases] =>
        summon[A =:= (d ** Enum[cases])]
        summon[B =:= Enum[dCases]]
        visualizeDistNAryLR(d.dist)

      case d: FlowAST.DistributeNAryRL[op, d, cases, dCases] =>
        summon[A =:= (Enum[cases] ** d)]
        summon[B =:= Enum[dCases]]
        visualizeDistNAryRL(d.dist)

      case i: FlowAST.Inject[op, lbl, x, cases] =>
        summon[A =:= x]
        summon[B =:= Enum[cases]]

        Exists(Exists((
          lump[A],
          lump[B],
          Visualization.LabeledBox(EdgeDesc.wire, EdgeDesc.wire, i.i.label.value + "(_)", fill = Some(Color.rgb(200, 200, 200)))
        )))

      case other =>
        Visualizer.unimplemented(other.getClass.getSimpleName())
  }

  private def visualizeDistNAryLR[D, Cases, DCases](
    dist: DistributionNAry.DistLR[**, ||, ::, D, Cases] { type Out = DCases },
  ): Exists[[X] =>> Exists[[Y] =>> (
    X Approximates (D ** Enum[Cases]),
    Y Approximates Enum[DCases],
    Visualization[X, Y],
  )]] =
    dist.dropNames[Tuple2, EmptyTuple] match {
      case Exists.Some(Exists.Some((x, dist, y))) =>
        VisualizeDistNAry[[a, b] =>> b ** a](
          [X, Y, A, B] => (fx: X Approximates A, fy: Y Approximates B) => fy ** fx,
          [X, D] => (x: EdgeDesc[X], d: EdgeDesc[D]) => d ** x,
          [X] => _ ?=> EdgeSegment.pickR,
          [X] => _ ?=> EdgeSegment.pickL,
        )(x, y, dist.kernel)
    }

  private def visualizeDistNAryRL[D, Cases, DCases](
    dist: DistributionNAry.DistRL[**, ||, ::, D, Cases] { type Out = DCases },
  ): Exists[[X] =>> Exists[[Y] =>> (
    X Approximates (Enum[Cases] ** D),
    Y Approximates Enum[DCases],
    Visualization[X, Y],
  )]] =
    dist.dropNames[Tuple2, EmptyTuple] match {
      case Exists.Some(Exists.Some((x, dist, y))) =>
        VisualizeDistNAry[**](
          [X, Y, A, B] => (fx: X Approximates A, fy: Y Approximates B) => fx ** fy,
          [X, D] => (x: EdgeDesc[X], d: EdgeDesc[D]) => x ** d,
          [X] => _ ?=> EdgeSegment.pickL,
          [X] => _ ?=> EdgeSegment.pickR,
        )(x, y, dist.kernel)
    }

  private class VisualizeDistNAry[<>[_, _]](
    parApprox: [X, Y, A, B] => (X Approximates A, Y Approximates B) => (X <> Y) Approximates (A <> B),
    liftEdgeDesc: [X, D] => (EdgeDesc[X], EdgeDesc[D]) => EdgeDesc[X <> D],
    pickCase: [X] => DummyImplicit ?=> EdgeSegment[X, X <> Wire],
    pickWire: [X] => DummyImplicit ?=> EdgeSegment[Wire, X <> Wire],
  ) {
    def apply[D, Cases, DCases, As, Bs](
      as: DropNames[||, ::, Tuple2, EmptyTuple, Cases, As],
      bs: DropNames[||, ::, Tuple2, EmptyTuple, DCases, Bs],
      distKernel: ParN[Tuple2, EmptyTuple, [x, y] =>> x <> D =:= y, As, Bs]
    ): Exists[[X] =>> Exists[[Y] =>> (
      X Approximates (Enum[Cases] <> D),
      Y Approximates Enum[DCases],
      Visualization[X, Y],
    )]] =
      distKernel.divide3[
        [A, X] =>> X Approximates A,
        [X, Y] =>> (X =:= Wire, Y =:= Wire <> Wire),
        [Y, B] =>> Y Approximates B,
      ](
        [A, B] => (ev: (A <> D) =:= B) => ev match { case TypeEq(Refl()) =>
          Exists(Exists((
            lump[A],
            (summon[Wire =:= Wire], summon[Wire <> Wire =:= Wire <> Wire]),
            parApprox(lump[A], lump[D]),
          )))
        }
      ) match {
        case ex @ Exists.Some(ey @ Exists.Some((x, core, y))) =>
          type Xs = ex.T
          type Ys = ey.T
          Exists(Exists((
            parApprox(Approximates.ParNDropNames(OpTag[Enum], as, x.flip), lump[D]),
            Approximates.ParNDropNames(OpTag[Enum], bs, y),
            go[Xs, Ys](core),
          )))
      }

    private def go[Xs, Ys](
      core: ParN[Tuple2, EmptyTuple, [X, Y] =>> (X =:= Wire, Y =:= Wire <> Wire), Xs, Ys],
    ): Visualization[Enum[Xs] <> Wire, Enum[Ys]] = {
      import EdgeSegment.{InElem, elem}

      val dxs: EdgeDesc[Enum[Xs]] =
        EdgeDesc.TupleN.make(
          OpTag[Enum],
          core.inputProjection[EdgeDesc]([x, y] => f => f match { case (TypeEq(Refl()), _) => wire })
        )
      val dys: EdgeDesc[Enum[Ys]] =
        EdgeDesc.TupleN.make(
          OpTag[Enum],
          core.outputProjection[EdgeDesc]([x, y] => f => f match { case (_, TypeEq(Refl())) => liftEdgeDesc(wire, wire) })
        )
      val elems: List[(
        TupleElem[Tuple2, EmptyTuple, Wire, Xs],
        TupleElem[Tuple2, EmptyTuple, Wire <> Wire, Ys],
      )] =
        core.zipWithIndex.toList(
          [x, y] => f => f match {
            case ((TypeEq(Refl()), TypeEq(Refl())), xi, yi) => (
              xi: TupleElem[Tuple2, EmptyTuple, Wire, Xs],
              yi: TupleElem[Tuple2, EmptyTuple, Wire <> Wire, Ys]
            )
          }
        )
      val (
        casesConnectors: List[Connector[Enum[Xs] <> Wire, Enum[Ys]]],
        casesAreas:  List[TrapezoidArea[Enum[Xs] <> Wire, Enum[Ys]]],
      ) =
        elems.zipWithIndex.map { case ((x, y), i) =>
          val segX: EdgeSegment[Wire, Enum[Xs] <> Wire] = pickCase[Enum[Xs]] compose elem(x)
          val segY: EdgeSegment[Wire <> Wire, Enum[Ys]] = elem(y)
          (
            Across(segX, segY compose pickCase[Wire]),
            TrapezoidArea(segX, segY, if i % 2 == 0 then ColorCaseLeft else ColorCaseRight),
          )
        }
        .unzip
      val distributeeConnectors: List[Connector[Enum[Xs] <> Wire, Enum[Ys]]] =
        elems.map { case (x, y) =>
          Across(pickWire[Enum[Xs]], InElem(pickWire[Wire], y))
            .fill(GradientVerticalWhiteBlack)
        }
      Visualization.WithBackgroundBox(
        fill = None,
        stroke = Some(Color.Black),
        Visualization.connectors(
          liftEdgeDesc(dxs, wire),
          dys,
        )(
          (casesConnectors ++ casesAreas ++ distributeeConnectors)*
        )
      )
    }
  }

  private def visualizeHandlers[A, B](
    handlers: SinkNAryNamed[FlowAST[Op, _, _], ||, ::, A, B],
  ): Exists[[X] =>> Exists[[Y] =>> (
    X Approximates Enum[A],
    Y Approximates B,
    Visualization[X, Y]
  )]] =
    handlers.dropNames[Tuple2, EmptyTuple] match
      case ∃((dn, hs)) =>
        hs.divide3[
          [A, X] =>> X Approximates A,
          [X, Y] =>> Visualization[X, Y],
          [Y, B] =>> Y Approximates B,
        ](
          [a, b] => f => visualizeAst(f) match {
            case ∃(∃((x, y, vis))) => Exists(Exists((x, vis, y)))
          }
        ) match {
          case ∃(∃((ax, vs, yb))) =>
            visualizeMerge(yb) match
              case ∃((g, z)) =>
                Exists(Exists((
                  Approximates.ParNDropNames(OpTag[Enum], dn, ax.flip),
                  z,
                  Visualization.IParN.from(OpTag[Enum], vs) :: Visualization.Sequence(g),
                )))
        }

  private def visualizeMerge[X, B](
    fs: SinkNAry[Approximates, Tuple2, EmptyTuple, X, B],
  ): Exists[[Y] =>> (IVisualization[Enum[X], Flx, ?, Flx, Y], Y Approximates B)] =
    fs.pullback(
      [x, y, b] => (xb, yb) => xb greatestCommonCoarsening yb,
      [x, y] => xy => xy.inDesc,
    ) match {
      case Exists.Some((refinements, appr)) =>
        Exists((
          coarsenMerge(refinements.asSink),
          appr
        ))
    }

  private def coarsenMerge[X, Y](
    fs: SinkNAry[[x, y] =>> y IsRefinedBy x, Tuple2, EmptyTuple, X, Y],
  ): IVisualization[Enum[X], Flx, ?, Flx, Y] =
    coarsenings(fs) match
      case Exists.Some((coarsenings, segments, ysDesc, yDesc)) =>
        coarsenings :: Visualization.Sequence(
          merge(
            ysDesc,
            yDesc,
            segments
          )
        )

  private def merge[Ys, Y](
    ysDesc: EdgeDesc[Ys],
    yDesc: EdgeDesc[Y],
    segments: List[EdgeSegment[Y, Ys]],
  ): Visualization.FullyFlexi[Ys, Y] = {
    val tgtStretch = EdgeStretch.paddingMidpoints(yDesc)
    val areas =
      segments.zipWithIndex.map { case (seg, i) =>
        TrapezoidArea(
          EdgeStretch.segment(seg),
          tgtStretch,
          if i % 2 == 0
            then VerticalFadeOutLeft
            else VerticalFadeOutRight
        )
      }

    val yWires = wiresOf(yDesc)
    val wires =
      for
        seg  <- segments
        wire <- yWires
      yield
        val inSeg = seg.compose(wire)
        Connector.Across(inSeg, wire)

    Visualization.connectors(
      ysDesc,
      yDesc
    )((areas ++ wires)*)
  }

  private def coarsenings[X, Y](
    fs: SinkNAry[[x, y] =>> y IsRefinedBy x, Tuple2, EmptyTuple, X, Y],
  ): Exists[[Ys] =>> (
    Visualization.IVisualization[Enum[X], Flx, Skw, Flx, Enum[Ys]],
    List[EdgeSegment[Y, Enum[Ys]]],
    EdgeDesc[Enum[Ys]],
    EdgeDesc[Y],
  )] =
    coarseningComponents[X, Y](fs) match
      case Exists.Some((visComps, segs, ysComps, yDesc)) =>
        Exists((
          Visualization.IParN(OpTag[Enum], visComps),
          segs.reverse,
          EdgeDesc.TupleN(OpTag[Enum], ysComps),
          yDesc,
        ))

  private def coarseningComponents[X, Y](
    fs: SinkNAry[[x, y] =>> y IsRefinedBy x, Tuple2, EmptyTuple, X, Y],
  ): Exists[[Ys] =>> (
    Visualization.IParN.Components[X, Flx, Skw, Flx, Ys],
    List[EdgeSegment.InElem[Enum, Y, Y, Ys]],
    EdgeDesc.TupleN.Components[Ys],
    EdgeDesc[Y],
  )] =
    fs match
      case SinkNAry.Single(f) =>
        Exists((
          Visualization.IParN.Single(Visualization.Adapt(Adaptoid.collapse(f))),
          EdgeSegment.elem(TupleElem.single) :: Nil,
          EdgeDesc.TupleN.single(f.inDesc),
          f.inDesc
        ))
      case s: SinkNAry.Snoc[arr, sep, nil, init, z, b] =>
        summon[X =:= (init, z)]
        summon[Y =:= b]
        coarseningComponents[init, Y](s.init) match {
          case Exists.Some((visInit, segs, ysDesc, yDesc)) =>
            Exists((
              Visualization.IParN.Snoc(visInit, Visualization.Adapt(Adaptoid.collapse(s.last))),
              EdgeSegment.elem(TupleElem.Last()) :: segs.map(_.inInit),
              EdgeDesc.TupleN.snoc(ysDesc, s.last.inDesc),
              yDesc
            ))
        }

  private def wiresOf[X](x: EdgeDesc[X]): List[WirePick[X]] =
    x match
      case EdgeDesc.SingleWire =>
        WirePick.pickId :: Nil
      case x: EdgeDesc.Binary[op, x1, x2] =>
        wiresOf(x.x1).map(_.inl[op, x2]) ++ wiresOf(x.x2).map(_.inr[op, x1])
}