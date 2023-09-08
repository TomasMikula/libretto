package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.examples.workflow.generic.lang.{**, FlowAST}
import libretto.lambda.{Capture, Focus, Shuffled, Spine}
import libretto.lambda.examples.workflow.generic.runtime.Input.FindValueRes
import libretto.lambda.util.{SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl

sealed trait WorkflowInProgress[Action[_, _], Val[_], A]

object WorkflowInProgress {
  case class Completed[Action[_, _], Val[_], A](result: Value[Val, A]) extends WorkflowInProgress[Action, Val, A]

  sealed trait Incomplete[Action[_, _], Val[_], A] extends WorkflowInProgress[Action, Val, A] {
    def crank: CrankRes[Action, Val, A]
  }

  case class IncompleteImpl[Action[_, _], Val[_], X, Y, A](
    input: Input[Val, X],
    cont: WIP.Closure[Action, Val, X, Y],
    resultAcc: Capture[**, Value[Val, _], Y, A],
  ) extends Incomplete[Action, Val, A] {
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
      case FedTo(pre, v, f, g, post) =>
        // depending on `v`, either
        //  - capture value and call it progress; or
        //  - ask for action execution
        throw NotImplementedError(s"at ${summon[SourcePos]}")
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
