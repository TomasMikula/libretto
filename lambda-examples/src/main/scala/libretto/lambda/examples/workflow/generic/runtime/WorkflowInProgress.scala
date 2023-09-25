package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.examples.workflow.generic.lang.{**, FlowAST}
import libretto.lambda.{Capture, Focus, Shuffled, Spine}
import libretto.lambda.examples.workflow.generic.runtime.Input.FindValueRes
import libretto.lambda.util.{SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl

sealed trait WorkflowInProgress[Action[_, _], Val[_], A] {
  import WorkflowInProgress.*

  def isReducible: Boolean

  def resultOpt: Option[WorkflowResult[Val, A]] =
    this match
      case Completed(result)       => Some(WorkflowResult.Success(result))
      case IncompleteImpl(_, _, _) => None

}

object WorkflowInProgress {
  case class Completed[Action[_, _], Val[_], A](result: Value[Val, A]) extends WorkflowInProgress[Action, Val, A]:
    override def isReducible: Boolean = false

  sealed trait Incomplete[Action[_, _], Val[_], A] extends WorkflowInProgress[Action, Val, A] {
    def crank: CrankRes[Action, Val, A]
  }

  case class IncompleteImpl[Action[_, _], Val[_], X, Y, A](
    input: Input[Val, X],
    cont: WIP.Closure[Action, Val, X, Y],
    resultAcc: Capture[**, Value[Val, _], Y, A],
  ) extends Incomplete[Action, Val, A] {
    override def isReducible: Boolean =
      input.isPartiallyReady

    override def crank: CrankRes[Action, Val, A] =
      input match
        case i @ Input.Awaiting(_) =>
          CrankRes.AlreadyStuck(this)
        case i =>
          input.findValue match
            case FindValueRes.NotFound(awaiting) =>
              CrankRes.Progressed(IncompleteImpl(Input.Awaiting(awaiting), cont, resultAcc))
            case FindValueRes.Found(path, value, TypeEq(Refl())) =>
              propagateValue(value, path, cont, resultAcc)

  }

  def init[Action[_, _], Val[_], A, B](
    input: Value[Val, A],
    wf: FlowAST[Action, A, B],
  ): WorkflowInProgress[Action, Val, B] =
    IncompleteImpl(
      Input.Ready(input),
      WIP.Closure.pure(wf),
      Capture.NoCapture(),
    )

  private type Shuffled[Action[_, _], Val[_]] =
    libretto.lambda.Shuffled[FlowAST.Work[WIP.PartiallyAppliedAction[Action, Val, _, _], _, _], **]

  private def propagateValue[Action[_, _], Val[_], F[_], A, B, C](
    value: Value[Val, A],
    remainingInput: Spine[**, Input[Val, _], F],
    cont: WIP.Closure[Action, Val, F[A], B],
    resultAcc: Capture[**, Value[Val, _], B, C],
  ): CrankRes[Action, Val, C] = {
    given sh: Shuffled[Action, Val] =
      WIP.Closure.shuffled[Action, Val]

    import sh.ChaseFwRes.*

    cont.toShuffled.chaseFw(remainingInput.focus) match
      case Transported(s, g, ev) =>
        accumulateResult(value, resultAcc.from(using ev), g, remainingInput, s)
      case Split(ev1) =>
        // split value and continue with a half
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case r: FedTo[f, x, v, w, g, b] => //(pre, v, f, g, post) =>
        def go[X, V[_], G[_], W](
          pre: [x] => Unit => sh.Shuffled[F[x], G[V[x]]],
          v: Focus[**, V],
          f: FlowAST.Work[WIP.PartiallyAppliedAction[Action, Val, *, *], V[X], W],
          g: Focus[**, G],
          post: sh.Shuffled[G[W], B]
        ): CrankRes[Action, Val, C] =
          // depending on `v`, either
          //  - capture value and call it progress; or
          //  - ask for action execution
          throw NotImplementedError(s"$r (at ${summon[SourcePos]})")

        go[x, v, g, w](r.pre, r.v, r.f, r.g, r.post)
  }

  private def accumulateResult[Action[_, _], Val[_], F[_], G[_], A, B](using
    sh: Shuffled[Action, Val],
  )(
    newResult: Value[Val, A],
    resultAcc: Capture[**, Value[Val, _], G[A], B],
    g: Focus[**, G],
    remainingInput: Spine[**, Input[Val, _], F],
    cont: [x] => Unit => sh.Shuffled[F[x], G[x]],
  ): CrankRes[Action, Val, B] =
    // feed `value` into `resultAcc`
    throw NotImplementedError(s"at ${summon[SourcePos]}")

  enum CrankRes[Action[_, _], Val[_], A]:
    case AlreadyStuck(w: WorkflowInProgress.Incomplete[Action, Val, A])
    case Progressed(w: WorkflowInProgress[Action, Val, A])
}
