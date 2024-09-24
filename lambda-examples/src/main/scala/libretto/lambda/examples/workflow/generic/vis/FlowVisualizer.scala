package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.lang.{++, **, FlowAST, Workflows}
import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.{Some as ∃}

import IOProportions.EdgeProportions

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

  extension [A, B](f: F[A, B])
    override def visualize =
      visualizeAst(f.ast)

  private def visualizeAst[A, B](f: FlowAST[Op, A, B]): Exists[[X] =>> Exists[[Y] =>> (
      X Approximates A,
      Y Approximates B,
      Visualization[X, Y]
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
            Exists(Exists((x1 pair x2, y1 pair y2, Visualization.Par(vg, vh))))
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
                        Visualization.par[++](vg, vh),
                        Morph.par[++](Morph.Unrefine(w1), Morph.Unrefine(w2)),
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
                      Visualization.Unimplemented("do"),
                      Morph.id(using x.inDesc),
                      vg,
                    ),
                    Morph.id(using xy.inDesc),
                    Visualization.Unimplemented("whileLeft"),
                  )
                )))
      case _: FlowAST.Swap[op, x, y] =>
        summon[A =:= (x ** y)]
        summon[B =:= (y ** x)]
        val v: (Wire ** Wire) Approximates A = Approximates.Initial[x]() pair Approximates.Initial[y]()
        val w: (Wire ** Wire) Approximates B = Approximates.Initial[y]() pair Approximates.Initial[x]()
        Exists(Exists((
          v,
          w,
          Visualization.connectors(
            EdgeProportions.unitWire pair EdgeProportions.unitWire,
            EdgeProportions.unitWire pair EdgeProportions.unitWire,
          )(
            Connector.Across(WirePick.pickL, WirePick.pickR),
            Connector.Across(WirePick.pickR, WirePick.pickL),
          )
        )))
      case other =>
        Visualizer.unimplemented(other.getClass.getSimpleName())
}