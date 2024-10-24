package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.lang.{++, **, ::, ||, Enum, FlowAST, Workflows}
import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.{Some as ∃}

import Approximates.lump
import Connector.{Across, NoEntryOut, StudIn, StudOut}
import DefaultDimensions.Length
import EdgeDesc.wire
import IOProportions.EdgeProportions
import PredefinedFill.{GradientVerticalWhiteBlack, VerticalFadeOutLeft, VerticalFadeOutRight}
import StyleDefs.{ColorCaseLeft, ColorCaseRight}
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

      case _: FlowAST.InjectL[op, x, y] =>
        summon[A =:= x]
        summon[B =:= (x ++ y)]

        Exists(Exists((
          lump[A],
          lump[x] ++ lump[y],
          Visualization.connectors(
            wire,
            wire ++ wire,
          )(
            TrapezoidArea(EdgeStretch.wireLHalf, EdgeStretch.pickL, ColorCaseLeft),
            TrapezoidArea(EdgeStretch.wireRHalf, EdgeStretch.pickR, Color.White),
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
            wire,
            wire ++ wire,
          )(
            TrapezoidArea(EdgeStretch.wireRHalf, EdgeStretch.pickR, ColorCaseRight),
            TrapezoidArea(EdgeStretch.wireLHalf, EdgeStretch.pickL, Color.White),
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
                      Visualization.Sequence(
                        Visualization.par[++](vg, vh),
                        Visualization.Adapt(Adaptoid.par[++](Adaptoid.collapse(w1), Adaptoid.collapse(w2))), // TODO: avoid if identity
                        merge(w1.inDesc),
                      ),
                    )))

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
                  Connector.Across(pickR.inr, pickId),
                  Connector.LoopIn(pickL.inr, pickL),
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
              wire ** (wire ++ wire),
              (wire ** wire) ++ (wire ** wire),
            )(
              Across(pickL.inr, pickR.inl),
              Across(pickR.inr, pickR.inr),
              TrapezoidArea(EdgeStretch.pickL.inr, EdgeStretch.pickL, ColorCaseLeft),
              TrapezoidArea(EdgeStretch.pickR.inr, EdgeStretch.pickR, ColorCaseRight),
              Across(pickL, pickL.inl).fill(GradientVerticalWhiteBlack),
              Across(pickL, pickL.inr).fill(GradientVerticalWhiteBlack),
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

      case _: FlowAST.Peel[op, init, lbl, z] =>
        summon[A =:= Enum[init || (lbl :: z)]]
        summon[B =:= (Enum[init] ++ z)]

        Exists(Exists((
          lump[A],
          lump[Enum[init]] ++ lump[z],
          Visualization.connectors(
            wire,
            wire ++ wire,
          )(
            TrapezoidArea(EdgeStretch.wireLHalf, EdgeStretch.pickL, ColorCaseLeft),
            TrapezoidArea(EdgeStretch.wireRHalf, EdgeStretch.pickR, ColorCaseRight),
            Across(pickId, pickL),
            Across(pickId, pickR),
          )
        )))

      case _: FlowAST.Unpeel[op, init, lbl, z] =>
        summon[A =:= (Enum[init] ++ z)]
        summon[B =:= Enum[init || (lbl :: z)]]

        Exists(Exists((
          lump[Enum[init]] ++ lump[z],
          lump[B],
          Visualization.connectors(
            wire ++ wire,
            wire,
          )(
            TrapezoidArea(EdgeStretch.pickL, EdgeStretch.wireLHalf, ColorCaseLeft),
            TrapezoidArea(EdgeStretch.pickR, EdgeStretch.wireRHalf, ColorCaseRight),
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
            wire,
            wire,
          )(
            Across(pickId, pickId)
          )
        )))

      case other =>
        Visualizer.unimplemented(other.getClass.getSimpleName())
  }

  def merge[X](x: EdgeDesc[X]): Visualization[X ++ X, X] =
    val tgt = EdgeStretch.paddingMidpoints(x)
    Visualization.connectors(
      x ++ x,
      x
    )(
      List(
        TrapezoidArea(EdgeStretch.pickL, tgt, VerticalFadeOutLeft),
        TrapezoidArea(EdgeStretch.pickR, tgt, VerticalFadeOutRight),
      ) ++
      wiresOf(x)
        .flatMap { i =>
          List(
            Connector.Across(i.inl, i),
            Connector.Across(i.inr, i),
          )
        } *
    )

  private def wiresOf[X](x: EdgeDesc[X]): List[WirePick[X]] =
    x match
      case EdgeDesc.SingleWire =>
        WirePick.pickId :: Nil
      case x: EdgeDesc.Binary[op, x1, x2] =>
        wiresOf(x.x1).map(_.inl[op, x2]) ++ wiresOf(x.x2).map(_.inr[op, x1])
}