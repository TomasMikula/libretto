package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{Capture, Unzippable}
import libretto.lambda.examples.workflow.generic.lang.{**, FlowAST}
import libretto.lambda.examples.workflow.generic.runtime.WIP.Irreducible.PartialResult
import libretto.lambda.util.SourcePos

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
      case Irreducible.Zip(w1, w2) => None
      case Zip(a1, a2) => None
      case Map(a, f) => None

  def crank(using Unzippable[**, Val]): CrankRes[Action, Val, A]

  def dup: WIP[Action, Val, A ** A]
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
    def ssc[Action[_, _], Val[_]] = summon[libretto.lambda.SymmetricSemigroupalCategory[Closure[Action, Val, _, _], **]]

    def pure[Action[_, _], Val[_], A, B](f: FlowAST[Action, A, B]): Closure[Action, Val, A, B] =
      f.translate([x, y] => (f: Action[x, y]) => PartiallyAppliedAction.pure[Action, Val, x, y](f))

    def id[Action[_, _], Val[_], A]: Closure[Action, Val, A, A] =
      FlowAST.Id()

    def swap[Action[_, _], Val[_], A, B]: Closure[Action, Val, A ** B, B ** A] =
      FlowAST.Swap()

    def assocLR[Action[_, _], Val[_], A, B, C]: Closure[Action, Val, (A ** B) ** C, A ** (B ** C)] =
      FlowAST.AssocLR()

    def assocRL[Action[_, _], Val[_], A, B, C]: Closure[Action, Val, A ** (B ** C), (A ** B) ** C] =
      FlowAST.AssocRL()

    def fst[Action[_, _], Val[_], A, B, Y](f: Closure[Action, Val, A, B]): Closure[Action, Val, A ** Y, B ** Y] =
      ssc.fst(f)

    def snd[Action[_, _], Val[_], A, B, X](f: Closure[Action, Val, A, B]): Closure[Action, Val, X ** A, X ** B] =
      ssc.snd(f)

    def dup[Action[_, _], Val[_], A]: Closure[Action, Val, A, A ** A] =
      FlowAST.Dup()
  }

  case class Zip[Action[_, _], Val[_], A1, A2](
    a1: WIP[Action, Val, A1],
    a2: WIP[Action, Val, A2],
  ) extends WIP[Action, Val, A1 ** A2]:
    override def crank(using Unzippable[**, Val]): CrankRes[Action, Val, A1 ** A2] =
      a1.crank match
        case CrankRes.AlreadyIrreducible(w1) =>
          a2.crank match
            case CrankRes.AlreadyIrreducible(w2) =>
              CrankRes.Progressed(WIP.Irreducible.Zip(w1, w2))
            case CrankRes.Progressed(w2) =>
              CrankRes.Progressed(Zip(w1, w2))
            case CrankRes.Ask(cont) =>
              throw NotImplementedError(s"at ${summon[SourcePos]}")
            case CrankRes.ActionRequest(input, action, cont) =>
              throw NotImplementedError(s"at ${summon[SourcePos]}")
        case CrankRes.Progressed(a1) =>
          CrankRes.Progressed(Zip(a1, a2))
        case CrankRes.Ask(cont) =>
          throw NotImplementedError(s"at ${summon[SourcePos]}")
        case CrankRes.ActionRequest(input, action, cont) =>
          throw NotImplementedError(s"at ${summon[SourcePos]}")

    override def dup: WIP[Action, Val, (A1 ** A2) ** (A1 ** A2)] =
      Map(Zip(a1.dup, a2.dup), Closure.ssc[Action, Val].ixi)


  case class Map[Action[_, _], Val[_], A, B](a: WIP[Action, Val, A], f: Closure[Action, Val, A, B]) extends WIP[Action, Val, B]:
    override def crank(using Unzippable[**, Val]): CrankRes[Action, Val, B] =
      a.crank match
        case CrankRes.AlreadyIrreducible(w) =>
          w.partialResult match
            case PartialResult.NotAvailable(w) =>
              CrankRes.Progressed(Irreducible.Suspended.Map(w, f))
            case PartialResult.FullResult(value) =>
              evalStep(f, value) match
                case EvalStepRes.Done(value) =>
                  CrankRes.Progressed(WIP.Irreducible.Done(value))
                case EvalStepRes.Ask(cont) =>
                  CrankRes.Ask(cont)
                case other =>
                  throw NotImplementedError(s"$other (at ${summon[SourcePos]})")
            case PartialResult.Partial(x, y, g) =>
              evalStepPartial(g >>> f, x, y) match
                case EvalStepPartialRes.Progressed(w) =>
                  CrankRes.Progressed(w)
                case EvalStepPartialRes.Ask(cont) =>
                  throw NotImplementedError(s"at ${summon[SourcePos]}")

        case CrankRes.Progressed(a1) =>
          CrankRes.Progressed(Map(a1, f))
        case CrankRes.Ask(cont) =>
          throw NotImplementedError(s"at ${summon[SourcePos]}")
        case CrankRes.ActionRequest(input, action, cont) =>
          throw NotImplementedError(s"at ${summon[SourcePos]}")

    override def dup: WIP[Action, Val, B ** B] =
      Map(a, f >>> Closure.dup)


  sealed trait Irreducible[Action[_, _], Val[_], A] extends WIP[Action, Val, A]:
    import Irreducible.*

    override def crank(using Unzippable[**, Val]): CrankRes[Action, Val, A] =
      CrankRes.AlreadyIrreducible(this)

    def partialResult: PartialResult[Action, Val, A]
  end Irreducible

  object Irreducible:
    case class Done[Action[_, _], Val[_], A](value: Value[Val, A]) extends Irreducible[Action, Val, A]:
      override def partialResult: PartialResult[Action, Val, A] =
        PartialResult.FullResult(value)
      override def dup: WIP[Action, Val, A ** A] =
        Done(value ** value)

    /** Unlike [[WIP.Zip]], the consituents are already [[Irreducible]]. */
    case class Zip[Action[_, _], Val[_], A1, A2](
      a1: WIP.Irreducible[Action, Val, A1],
      a2: WIP.Irreducible[Action, Val, A2],
    ) extends WIP.Irreducible[Action, Val, A1 ** A2]:
      override def dup: WIP[Action, Val, (A1 ** A2) ** (A1 ** A2)] =
        WIP.Map(WIP.Zip(a1.dup, a2.dup), Closure.ssc.ixi)

      override def partialResult: PartialResult[Action, Val, A1 ** A2] =
        import PartialResult.*

        a1.partialResult match
          case NotAvailable(w1) =>
            a2.partialResult match
              case NotAvailable(w2) => NotAvailable(Suspended.Zip(w1, w2))
              case FullResult(a2)   => Partial(a2, w1, Closure.swap)
              case Partial(x, y, f) => Partial(x, Zip(y, w1), Closure.assocRL >>> Closure.swap >>> Closure.snd(f))
          case FullResult(a1) =>
            Partial(a1, a2, Closure.id)
          case Partial(x, y, f) =>
            Partial(x, Zip(y, a2), Closure.assocRL >>> Closure.fst(f))

    sealed trait Suspended[Action[_, _], Val[_], A] extends Irreducible[Action, Val, A]:
      override def partialResult: PartialResult[Action, Val, A] =
        PartialResult.NotAvailable(this)

    object Suspended {
      case class Awaiting[Action[_, _], Val[_], A](
        promise: PromiseId[A],
      ) extends Suspended[Action, Val, A]:
        override def dup: WIP[Action, Val, A ** A] =
          Zip(this, this)

      case class Map[Action[_, _], Val[_], A, B](
        a: Suspended[Action, Val, A],
        f: Closure[Action, Val, A, B],
      ) extends Suspended[Action, Val, B]:
        override def dup: WIP[Action, Val, B ** B] =
          Map(a, f >>> Closure.dup)

      /** Unlike [[WIP.Zip]] and [[Irreducible.Zip]], the consituents are both [[Suspended]]. */
      case class Zip[Action[_, _], Val[_], A1, A2](
        a1: Suspended[Action, Val, A1],
        a2: Suspended[Action, Val, A2],
      ) extends Suspended[Action, Val, A1 ** A2]:
        override def dup: WIP[Action, Val, A1 ** A2 ** (A1 ** A2)] =
          WIP.Map(WIP.Zip(a1.dup, a2.dup), Closure.ssc.ixi)
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
  )(using
    Unzippable[**, Val],
  ): EvalStepRes[Action, Val, B] =
    f match
      case FlowAST.Id() =>
        EvalStepRes.Done(input)

      case FlowAST.AndThen(f, g) =>
        evalStep(f, input) match
          case EvalStepRes.Done(value) =>
            evalStep(g, value)
          case ask: EvalStepRes.Ask[action, v, x, b] =>
            EvalStepRes.Ask { (px: PromiseId[x]) => WIP.Map(ask.cont(px), g) }
          case other =>
            throw NotImplementedError(s"$other (at ${summon[SourcePos]})")

      case FlowAST.AssocLR() => throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.AssocRL() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case f: FlowAST.Par[action, a1, a2, b1, b2] =>
        val (a1, a2) = Value.unpair[Val, a1, a2](input)
        evalStep(f.f1, a1) match
          case EvalStepRes.Done(b1) =>
            evalStep(f.f2, a2) match
              case EvalStepRes.Done(b2) =>
                EvalStepRes.Done(b1 ** b2)
              case ask: EvalStepRes.Ask[action_, v, x, b2_] =>
                EvalStepRes.Ask { (px: PromiseId[x]) =>
                  WIP.Zip(WIP.Irreducible.Done(b1), ask.cont(px))
                }
              case other =>
                throw NotImplementedError(s"$other (at ${summon[SourcePos]})")
          case ask: EvalStepRes.Ask[action_, v, x, b1_] =>
            EvalStepRes.Ask { (px: PromiseId[x]) =>
              WIP.Zip(ask.cont(px), WIP.Map(Irreducible.Done(a2), f.f2))
            }
          case other =>
            throw NotImplementedError(s"$other (at ${summon[SourcePos]})")

      case FlowAST.Swap() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.IntroFst() =>
        EvalStepRes.Done(Value.unit ** input)

      case FlowAST.Prj1() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.Prj2() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.Dup() =>
        EvalStepRes.Done(input ** input)

      case FlowAST.Either(f, g) =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.DistributeLR() =>throw NotImplementedError(s"at ${summon[SourcePos]}")

      case FlowAST.Promise() =>
        EvalStepRes.Ask { (pb: PromiseId[B]) => WIP.Irreducible.Suspended.Awaiting(pb) }

      case FlowAST.DomainAction(action) =>throw NotImplementedError(s"at ${summon[SourcePos]}")

  def evalStepPartial[Action[_, _], Val[_], A1, A2, B](
    f: Closure[Action, Val, A1 ** A2, B],
    a1: Value[Val, A1],
    a2: Irreducible[Action, Val, A2],
  )(using
    Unzippable[**, Val],
  ): EvalStepPartialRes[Action, Val, B] =
    f match
      case FlowAST.Id() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")

      case FlowAST.AndThen(f, g) =>
        evalStepPartial(f, a1, a2) match
          case EvalStepPartialRes.Progressed(w) =>
            EvalStepPartialRes.Progressed(WIP.Map(w, g))
          case ask: EvalStepPartialRes.Ask[action, v, x, b] =>
            EvalStepPartialRes.Ask { (px: PromiseId[x]) => WIP.Map(ask.cont(px), g) }
          case other =>
            throw NotImplementedError(s"$other (at ${summon[SourcePos]})")

      case FlowAST.AssocLR() => throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.AssocRL() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case f: FlowAST.Par[action, a1, a2, b1, b2] =>
        evalStep(f.f1, a1) match
          case EvalStepRes.Done(b1) =>
            throw NotImplementedError(s"at ${summon[SourcePos]}")
          case ask: EvalStepRes.Ask[action_, v, x, b1_] =>
            EvalStepPartialRes.Ask { (px: PromiseId[x]) =>
              WIP.Zip(ask.cont(px), WIP.Map(a2, f.f2))
            }
          case other =>
            throw NotImplementedError(s"$other (at ${summon[SourcePos]})")

      case FlowAST.Swap() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.IntroFst() =>
        EvalStepPartialRes.Progressed(
          WIP.Irreducible.Zip(
            WIP.Irreducible.Done(Value.unit),
            WIP.Irreducible.Zip(WIP.Irreducible.Done(a1), a2),
          )
        )

      case FlowAST.Prj1() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.Prj2() =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.Dup() =>
        EvalStepPartialRes.Progressed(
          WIP.Map(
            WIP.Zip(
              Irreducible.Zip(Irreducible.Done(a1), Irreducible.Done(a1)),
              a2.dup,
            ),
            Closure.ssc[Action, Val].ixi,
          )
        )

      case FlowAST.Either(f, g) =>throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FlowAST.DistributeLR() =>throw NotImplementedError(s"at ${summon[SourcePos]}")

      case FlowAST.Promise() =>
        EvalStepPartialRes.Ask { (pb: PromiseId[B]) => WIP.Irreducible.Suspended.Awaiting(pb) }

      case FlowAST.DomainAction(action) =>throw NotImplementedError(s"at ${summon[SourcePos]}")

  enum CrankRes[Action[_, _], Val[_], A] {
    case AlreadyIrreducible(w: WIP.Irreducible[Action, Val, A])
    case Progressed(w: WIP[Action, Val, A])
    case Ask[Action[_, _], Val[_], X, A](
      cont: PromiseId[X] => WIP[Action, Val, A],
    ) extends CrankRes[Action, Val, A]
    case ActionRequest[Action[_, _], Val[_], X, Y, A](
      input: Value[Val, X],
      action: Action[X, Y],
      cont: Promised[Y] => WIP[Action, Val, A],
    ) extends CrankRes[Action, Val, A]
  }

  enum EvalStepRes[Action[_, _], Val[_], A]:
    case Done(value: Value[Val, A])
    case Ask[Action[_, _], Val[_], X, A](
      cont: PromiseId[X] => WIP[Action, Val, A],
    ) extends EvalStepRes[Action, Val, A]

  enum EvalStepPartialRes[Action[_, _], Val[_], A]:
    case Progressed(w: WIP[Action, Val, A])
    case Ask[Action[_, _], Val[_], X, A](
      cont: PromiseId[X] => WIP[Action, Val, A],
    ) extends EvalStepPartialRes[Action, Val, A]
}
