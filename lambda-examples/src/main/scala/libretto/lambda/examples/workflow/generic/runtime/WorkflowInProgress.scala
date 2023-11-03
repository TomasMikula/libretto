package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{Capture, Focus, Knitted, Shuffled, Spine, Unzippable}
import libretto.lambda.examples.workflow.generic.lang.{**, ++, FlowAST, PortName, Reading, given}
import libretto.lambda.examples.workflow.generic.runtime.Input.FindValueRes
import libretto.lambda.examples.workflow.generic.runtime.{RuntimeFlows as rtf}
import libretto.lambda.util.{BiInjective, Exists, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.UnhandledCase
import scala.concurrent.duration.FiniteDuration

sealed trait WorkflowInProgress[Action[_, _], Val[_], A] {
  import WorkflowInProgress.*

  def isReducible: Boolean

  def resultOpt: Option[WorkflowResult[Val, A]] =
    this match
      case Completed(result)       => Some(WorkflowResult.Success(result))
      case IncompleteImpl(_, _, _) => None
      case Failed(_, _)            => None

}

object WorkflowInProgress {
  case class Completed[Action[_, _], Val[_], A](result: Value[Val, A]) extends WorkflowInProgress[Action, Val, A]:
    override def isReducible: Boolean = false

  case class Failed[Action[_, _], Val[_], A](
    error: Throwable,
    incomplete: Incomplete[Action, Val, A],
  ) extends WorkflowInProgress[Action, Val, A]:
    override def isReducible: Boolean = false

  sealed trait Incomplete[Action[_, _], Val[_], A] extends WorkflowInProgress[Action, Val, A] {
    def crank(using Value.Compliant[Val]): CrankRes[Action, Val, A]
  }

  case class IncompleteImpl[Action[_, _], Val[_], X, Y, A](
    input: Input[Val, X],
    cont: rtf.Flow[Action, Val, X, Y],
    resultAcc: Capture[**, Value[Val, _], Y, A],
  ) extends Incomplete[Action, Val, A] {
    override def isReducible: Boolean =
      input.isPartiallyReady

    override def crank(using Value.Compliant[Val]): CrankRes[Action, Val, A] =
      input match
        case i @ Input.Awaiting(_) =>
          CrankRes.AlreadyStuck(this)
        case i =>
          input.findValue match
            case FindValueRes.NotFound(awaiting) =>
              CrankRes.Progressed(IncompleteImpl(Input.Awaiting(awaiting), cont, resultAcc))
            case FindValueRes.Found(path, value, TypeEq(Refl())) =>
              import libretto.lambda.examples.workflow.generic.runtime.RuntimeFlows.{PropagateValueRes as pvr}
              rtf.propagateValue(value, path.focus, cont) match
                case tr: pvr.Transported[op, val_, f, x, g, y] =>
                  tr.outFocus match
                    case Focus.Id() =>
                      val result = resultAcc.complete(tr.outputValue.as(using tr.ev)).fold
                      CrankRes.Progressed(Completed(result))
                    case g: Focus.Proper[pr, g] =>
                      resultAcc.absorb(tr.outputValue, g)(using tr.ev) match
                        case Capture.Absorbed.Impl(k, resultAcc1) =>
                          tr.knit(k) match
                            case Exists.Some((k0, f)) =>
                              val input1 = path.knitFold(k0)
                              CrankRes.Progressed(IncompleteImpl(input1, f, resultAcc1))
                case pvr.Transformed(newInput, f) =>
                  CrankRes.Progressed(IncompleteImpl(path.plugFold(newInput), f, resultAcc))
                case pvr.Absorbed(k, f) =>
                  CrankRes.Progressed(IncompleteImpl(path.knitFold(k), f, resultAcc))
                case pvr.Shrunk(newInput, p, f) =>
                  val input1 = path.plugFold(newInput)
                  val input2 = input1.discard(p) // TODO: cancel running actions
                  CrankRes.Progressed(IncompleteImpl(input2, f, resultAcc))
                case pvr.Read(cont) =>
                  CrankRes.read(path, cont, resultAcc)
                case pvr.ReadAwaitTimeout(toAwait, timeout, cont) =>
                  val pId = Value.extractPortId(toAwait)
                  CrankRes.SetTimer(
                    timeout,
                    timerId => {
                      IncompleteImpl(
                        path.plugFold(Input.awaitingInput(pId, timerId)),
                        cont,
                        resultAcc,
                      )
                    },
                  )
                case pvr.ActionRequest(input, action, cont) =>
                  CrankRes.ActionRequest(
                    input,
                    action,
                    y => IncompleteImpl(
                      path.plugFold(y),
                      cont,
                      resultAcc,
                    ),
                  )
  }

  def init[Action[_, _], Val[_], A, B](
    input: Value[Val, A],
    wf: FlowAST[Action, A, B],
  ): WorkflowInProgress[Action, Val, B] =
    IncompleteImpl(
      Input.Ready(input),
      rtf.pure(wf),
      Capture.NoCapture(),
    )

  enum CrankRes[Action[_, _], Val[_], A]:
    case AlreadyStuck(w: WorkflowInProgress.Incomplete[Action, Val, A])
    case Progressed(w: WorkflowInProgress[Action, Val, A])
    case Ask[Action[_, _], Val[_], X, A](
      cont: (Input[Val, PortName[X]], Input[Val, Reading[X]]) => WorkflowInProgress[Action, Val, A],
    ) extends CrankRes[Action, Val, A]
    case SetTimer[Action[_, _], Val[_], A](
      duration: FiniteDuration,
      cont: TimerId => WorkflowInProgress[Action, Val, A],
    ) extends CrankRes[Action, Val, A]
    case ActionRequest[Action[_, _], Val[_], X, Y, A](
      input: Value[Val, X],
      action: Action[X, Y],
      cont: Input[Val, Y] => WorkflowInProgress[Action, Val, A],
    ) extends CrankRes[Action, Val, A]

  object CrankRes:
    def read[Action[_, _], Val[_], F[_], X, Y, A](
      remainingInput: Spine[**, Input[Val, _], F],
      cont: rtf.Flow[Action, Val, F[PortName[X] ** Reading[X]], Y],
      resultAcc: Capture[**, Value[Val, _], Y, A],
    ): CrankRes[Action, Val, A] =
      CrankRes.Ask[Action, Val, X, A] { (px, rx) =>
        val newInput = remainingInput.plugFold(px ** rx)
        IncompleteImpl(newInput, cont, resultAcc)
      }
}
