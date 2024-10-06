package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.lang.{++, **, ::, ||, Enum, FlowAST, Workflows}
import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.{Some as ∃}

import Approximates.lump
import Connector.{Across, NoEntryOut, StudIn, StudOut}
import DefaultDimensions.Length
import IOProportions.EdgeProportions
import EdgeProportions.unitSize
import WirePick.{pickId, pickL, pickR}

object FlowVisualizer {
  def apply[Op[_, _]](using
    workflows: Workflows[Op],
    visOp: Visualizer[Op, Approximates],
  ): FlowVisualizer[Op, workflows.Flow] =
    new FlowVisualizer[Op, workflows.Flow]

  private[FlowVisualizer] val ColorCaseLeft  = Color.rgba(0, 119, 183, 0.25)
  private[FlowVisualizer] val ColorCaseRight = Color.rgba(252, 190, 51, 0.25)
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
  )]] =
    f match
      case FlowAST.Ext(action) =>
        action.visualize

      case FlowAST.AndThen(g, h) =>
        (visualizeAst(g), visualizeAst(h)) match
          case (∃(∃((x, y1, vg))), ∃(∃((y2, z, vh)))) =>
            (y1 unify y2) match
              case ∃((y, y1, y2)) =>
                val m = y1 morph y2
                Exists(Exists((x, z, Visualization.Seq(vg, m, vh))))

      case FlowAST.Par(g, h) =>
        (visualizeAst(g), visualizeAst(h)) match
          case (∃(∃((x1, y1, vg))), ∃(∃((x2, y2, vh)))) =>
            Exists(Exists((x1 ** x2, y1 ** y2, Visualization.Par(vg, vh))))

      case _: FlowAST.InjectL[op, x, y] =>
        summon[A =:= x]
        summon[B =:= (x ++ y)]

        Exists(Exists((
          lump[A],
          lump[x] ++ lump[y],
          Visualization.connectors(
            unitSize,
            unitSize ∙ unitSize,
          )(
            TrapezoidArea(pickId.midpoint, pickL.post, ColorCaseLeft),
            TrapezoidArea(pickId.wireRHalf, pickR, Color.White),
            Across(pickId, pickL),
            NoEntryOut(pickR),
          )
        )))

      case _: FlowAST.InjectR[op, x, y] =>
        summon[A =:= y]
        summon[B =:= (x ++ y)]

        Exists(Exists((
          lump[A],
          lump[x] ++ lump[y],
          Visualization.connectors(
            unitSize,
            unitSize ∙ unitSize,
          )(
            TrapezoidArea(pickId.midpoint, pickR.pre, ColorCaseRight),
            TrapezoidArea(pickId.wireLHalf, pickL, Color.White),
            Across(pickId, pickR),
            NoEntryOut(pickL),
          )
        )))

      case FlowAST.Either(g, h) =>
        (visualizeAst(g), visualizeAst(h)) match
          case (∃(∃((x, z1, vg))), ∃(∃((y, z2, vh)))) =>
            (z1 unify z2) match
              case ∃((z, zz1, zz2)) =>
                (zz1 greatestCommonCoarsening zz2) match
                  case ∃((w1, w2)) =>
                    Exists(Exists((
                      x ++ y,
                      z1 coarsenBy w1, // could equivalently use `z2 coarsenBy w2`
                      Visualization.Seq(
                        Visualization.par[++](vg.withBackground(ColorCaseLeft), vh.withBackground(ColorCaseRight)),
                        Adaptoid.par[++](Adaptoid.Collapse(w1), Adaptoid.Collapse(w2)),
                        Visualization.merge2(EdgeProportions.default(w1.inDesc)),
                      ),
                    )))

      case FlowAST.DoWhile(g) =>
        visualizeAst(g) match
          case ∃(∃((x, xy, vg))) =>
            Approximates.unplus(xy) match
              case ∃(∃((x1, y, _))) =>
                Exists(Exists((
                  x,
                  y,
                  Visualization.Seq(
                    Visualization.Seq(
                      Visualization.Unimplemented("do", x.inDesc, x.inDesc),
                      Adaptoid.id(using x.inDesc),
                      vg,
                    ),
                    Adaptoid.id(using xy.inDesc),
                    Visualization.Unimplemented("whileLeft", xy.inDesc, y.inDesc),
                  )
                )))

      case FlowAST.Id() =>
        summon[A =:= B]
        Exists(Exists((
          lump[A],
          lump[B],
          Visualization.connectors(
            unitSize,
            unitSize,
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
            unitSize ∙ unitSize,
            unitSize ∙ unitSize,
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
            (unitSize ∙ unitSize) ∙ unitSize,
            unitSize ∙ (unitSize ∙ unitSize),
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
            unitSize ∙ (unitSize ∙ unitSize),
            (unitSize ∙ unitSize) ∙ unitSize,
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
            unitSize ∙ unitSize,
            unitSize,
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
            unitSize ∙ unitSize,
            unitSize,
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
            unitSize,
            unitSize ∙ unitSize,
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
              unitSize,
              unitSize ∙ unitSize,
            )
          )(
            Across(pickId, pickL),
            Across(pickId, pickR),
          )
        )))

      case _: FlowAST.DistributeLR[op, x, y, z] =>
        summon[A =:= x ** (y ++ z)]
        summon[B =:= (x ** y) ++ (x ** z)]

        Exists(Exists((
          lump[x] ** (lump[y] ++ lump[z]),
          (lump[x] ** lump[y]) ++ (lump[x] ** lump[z]),
          Visualization.WithBackgroundBox(
            fill = None,
            stroke = Some(Color.Black),
            Visualization.connectors(
              unitSize ∙ (unitSize ∙ unitSize),
              (unitSize ∙ unitSize) ∙ (unitSize ∙ unitSize),
            )(
              Across(pickL.inr, pickR.inl),
              Across(pickR.inr, pickR.inr),
              TrapezoidArea(EdgeSegment.pickL.inr, EdgeSegment.pickL, ColorCaseLeft),
              TrapezoidArea(EdgeSegment.pickR.inr, EdgeSegment.pickR, ColorCaseRight),
              Across(pickL, pickL.inl).fill(PredefinedFill.GradientVerticalWhiteBlack),
              Across(pickL, pickL.inr).fill(PredefinedFill.GradientVerticalWhiteBlack),
            )
          )
        )))

      case i: FlowAST.Inject[op, lbl, x, cases] =>
        summon[A =:= x]
        summon[B =:= Enum[cases]]

        Exists(Exists((
          lump[A],
          lump[B],
          Visualization.LabeledBox(EdgeDesc.wire, EdgeDesc.wire, i.i.label + "(_)", fill = Some(Color.rgb(200, 200, 200)))
        )))

      case _: FlowAST.Peel[op, lbl, h, cases] =>
        summon[A =:= Enum[cases || (lbl :: h)]]
        summon[B =:= (h ++ Enum[cases])]

        Exists(Exists((
          lump[A],
          lump[h] ++ lump[Enum[cases]],
          Visualization.connectors(
            unitSize,
            unitSize ∙ unitSize,
          )(
            TrapezoidArea(WirePick.pickId.midpoint, WirePick.pickL.post, ColorCaseLeft),
            TrapezoidArea(WirePick.pickId.midpoint, WirePick.pickR.pre, ColorCaseRight),
            Across(pickId, pickL),
            Across(pickId, pickR),
          )
        )))

      case _: FlowAST.Unpeel[op, lbl, h, cases] =>
        summon[A =:= (h ++ Enum[cases])]
        summon[B =:= Enum[cases || (lbl :: h)]]

        Exists(Exists((
          lump[h] ++ lump[Enum[cases]],
          lump[B],
          Visualization.connectors(
            unitSize ∙ unitSize,
            unitSize,
          )(
            TrapezoidArea(WirePick.pickL.post, WirePick.pickId.midpoint, ColorCaseLeft),
            TrapezoidArea(WirePick.pickR.pre, WirePick.pickId.midpoint, ColorCaseRight),
            Across(pickL, pickId),
            Across(pickR, pickId),
          )
        )))

      case _: FlowAST.Extract[op, lbl, h] =>
        summon[A =:= Enum[lbl :: h]]
        summon[B =:= h]

        Exists(Exists((
          lump[A],
          lump[B],
          Visualization.connectors(
            unitSize,
            unitSize,
          )(
            Across(pickId, pickId)
          )
        )))

      case other =>
        Visualizer.unimplemented(other.getClass.getSimpleName())
}