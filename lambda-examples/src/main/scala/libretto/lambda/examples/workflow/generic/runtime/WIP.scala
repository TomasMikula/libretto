package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.Capture
import libretto.lambda.examples.workflow.generic.lang.{**, FlowAST}
import libretto.lambda.util.SourcePos
import libretto.lambda.examples.workflow.generic.runtime.WIP.Irreducible.PartialResult

sealed trait WIP[Action[_, _], Val[_], A] {
  import WIP.*

  def isReducible: Boolean =
    this match {
      case _: Irreducible[Action, Val, A] => false
      case Zip(_, _) => true
      case Map(_, _) => true
    }

  def resultOpt: Option[WorkflowResult[Val, A]] =
    this match
      case Irreducible.Done(value) => Some(WorkflowResult.Success(value))
      case _: Irreducible.Suspended[Action, Val, A] => None
      case Zip(a1, a2) => None
      case Map(a, f) => None

  def crank: CrankRes[Action, Val, A]
}

object WIP {
  enum PartiallyAppliedAction[Action[_, _], Val[_], A, B]:
    case Impl[Action[_, _], Val[_], A, X, B](
      args: Capture[**, Val, A, X],
      f: Action[X, B],
    ) extends PartiallyAppliedAction[Action, Val, A, B]

  object PartiallyAppliedAction {
    def pure[Action[_, _], Val[_], A, B](f: Action[A, B]): PartiallyAppliedAction[Action, Val, A, B] =
      PartiallyAppliedAction.Impl(Capture.NoCapture(), f)
  }

  type Closure[Action[_, _], Val[_], A, B] = FlowAST[PartiallyAppliedAction[Action, Val, _, _], A, B]
  object Closure {
    def pure[Action[_, _], Val[_], A, B](f: FlowAST[Action, A, B]): Closure[Action, Val, A, B] =
      f.translate([x, y] => (f: Action[x, y]) => PartiallyAppliedAction.pure[Action, Val, x, y](f))
  }

  case class Zip[Action[_, _], Val[_], A1, A2](
    a1: WIP[Action, Val, A1],
    a2: WIP[Action, Val, A2],
  ) extends WIP[Action, Val, A1 ** A2]:
    override def crank: CrankRes[Action, Val, A1 ** A2] =
      a1.crank match
        case CrankRes.AlreadyIrreducible(w) =>
          throw NotImplementedError(s"at ${summon[SourcePos]}")
        case CrankRes.Progressed(a1) =>
          CrankRes.Progressed(Zip(a1, a2))
        case CrankRes.ActionRequest(input, action, cont) =>
          throw NotImplementedError(s"at ${summon[SourcePos]}")


  case class Map[Action[_, _], Val[_], A, B](a: WIP[Action, Val, A], f: Closure[Action, Val, A, B]) extends WIP[Action, Val, B]:
    override def crank: CrankRes[Action, Val, B] =
      a.crank match
        case CrankRes.AlreadyIrreducible(w) =>
          w.partialResult match
            case PartialResult.NotAvailable(w) =>
              CrankRes.Progressed(Irreducible.Suspended.Map(w, f))
            case PartialResult.FullResult(value) =>
              evalStep(f, value) match
                case EvalStepRes.Done(value) =>
                  CrankRes.Progressed(WIP.Irreducible.Done(value))
                case other =>
                  throw NotImplementedError(s"$other (at ${summon[SourcePos]})")
            case PartialResult.Partial(x, y, f) =>
              throw NotImplementedError(s"at ${summon[SourcePos]}")
        case CrankRes.Progressed(a1) =>
          CrankRes.Progressed(Map(a1, f))
        case CrankRes.ActionRequest(input, action, cont) =>
          throw NotImplementedError(s"at ${summon[SourcePos]}")


  sealed trait Irreducible[Action[_, _], Val[_], A] extends WIP[Action, Val, A]:
    import Irreducible.*

    override def crank: CrankRes[Action, Val, A] =
      CrankRes.AlreadyIrreducible(this)

    def partialResult: PartialResult[Action, Val, A]
  end Irreducible

  object Irreducible:
    case class Done[Action[_, _], Val[_], A](value: Value[Val, A]) extends Irreducible[Action, Val, A]:
      override def partialResult: PartialResult[Action, Val, A] =
        PartialResult.FullResult(value)

    sealed trait Suspended[Action[_, _], Val[_], A] extends Irreducible[Action, Val, A]:
      override def partialResult: PartialResult[Action, Val, A] =
        PartialResult.NotAvailable(this)

    object Suspended {
      case class Awaiting[Action[_, _], Val[_], A](promised: Promised[A]) extends Suspended[Action, Val, A]

      case class Map[Action[_, _], Val[_], A, B](
        a: Suspended[Action, Val, A],
        f: Closure[Action, Val, A, B],
      ) extends Suspended[Action, Val, B]
    }

    enum PartialResult[Action[_, _], Val[_], A]:
      case NotAvailable(w: Suspended[Action, Val, A])
      case FullResult(value: Value[Val, A])
      case Partial[Action[_, _], Val[_], X, Y, A](
        x: Value[Val, X],
        y: Irreducible[Action, Val, Y],
        f: Closure[Action, Val, X ** Y, A],
      ) extends PartialResult[Action, Val, A]
    end PartialResult
  end Irreducible

  def init[Action[_, _], Val[_], A, B](
    input: Value[Val, A],
    wf: FlowAST[Action, A, B],
  ): WIP[Action, Val, B] =
    Map(Irreducible.Done(input), Closure.pure(wf))

  def evalStep[Action[_, _], Val[_], A, B](
    f: Closure[Action, Val, A, B],
    input: Value[Val, A],
  ): EvalStepRes[Action, Val, B] =
    f match
      case FlowAST.Id() =>
        EvalStepRes.Done(input)
      case FlowAST.AndThen(f, g) =>
        evalStep(f, input) match
          case EvalStepRes.Done(value) =>
            evalStep(g, value)
          case other =>
            throw NotImplementedError(s"$other (at ${summon[SourcePos]})")
      case FlowAST.AssocLR() => throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.AssocRL() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.Par(f1, f2) =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.Swap() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.IntroFst() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.Prj1() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.Prj2() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.Dup() =>
        EvalStepRes.Done(input ** input)
      case FlowAST.Either(f, g) =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.DistributeLR() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.NewHttpReceptorEndpoint() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.DomainAction(action) =>throw NotImplementedError(s"at ${summon[SourcePos]}")


  enum CrankRes[Action[_, _], Val[_], A] {
    case AlreadyIrreducible(w: WIP.Irreducible[Action, Val, A])
    case Progressed(w: WIP[Action, Val, A])
    case ActionRequest[Action[_, _], Val[_], X, Y, A](
      input: Value[Val, X],
      action: Action[X, Y],
      cont: Promised[Y] => WIP[Action, Val, A],
    ) extends CrankRes[Action, Val, A]
  }

  enum EvalStepRes[Action[_, _], Val[_], A]:
    case Done(value: Value[Val, A])
}
