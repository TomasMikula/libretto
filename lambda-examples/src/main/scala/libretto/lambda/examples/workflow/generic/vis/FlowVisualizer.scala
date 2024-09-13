package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.lang.{FlowAST, Workflows}

object FlowVisualizer {
  def visualize[Op[_, _], A, B](using workflows: Workflows[Op])(f: workflows.Flow[A, B])(using Visualizable[Op]): Visualization =
    visualizeAst(f.ast)

  private def visualizeAst[Op[_, _], A, B](f: FlowAST[Op, A, B])(using Visualizable[Op]): Visualization =
    f match
      case FlowAST.Ext(action) =>
        action.visualize
      case FlowAST.AndThen(g, h) =>
        Visualization.Seq(visualizeAst(g), visualizeAst(h))
      case FlowAST.Par(g, h) =>
        Visualization.Par(visualizeAst(g), visualizeAst(h))
      case FlowAST.Either(g, h) =>
        // XXX: this is not a correct visualization of Either
        Visualization.Par(visualizeAst(g), visualizeAst(h))
      case other =>
        Visualization.Unimplemented(other.getClass.getSimpleName())
}