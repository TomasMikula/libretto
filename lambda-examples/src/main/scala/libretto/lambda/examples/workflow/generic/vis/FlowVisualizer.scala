package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.lang.{FlowAST, Workflows}

object FlowVisualizer {
  def visualize[Op[_, _], A, B](using workflows: Workflows[Op])(f: workflows.Flow[A, B])(using Visualizable[Op]): Visualization =
    workflows.astOf(f) match
      case FlowAST.Ext(action) => action.visualize
      case other => Visualization.Unimplemented(other.getClass.getSimpleName())
}