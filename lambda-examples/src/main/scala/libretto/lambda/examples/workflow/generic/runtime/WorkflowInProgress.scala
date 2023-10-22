package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{Capture, Focus, Knitted, Shuffled, Spine, Unzippable}
import libretto.lambda.examples.workflow.generic.lang.{**, ++, Due, FlowAST, PromiseRef, Promised, given}
import libretto.lambda.examples.workflow.generic.runtime.Input.FindValueRes
import libretto.lambda.util.{BiInjective, Exists, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.UnhandledCase

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
    def crank(using Unzippable[**, Val]): CrankRes[Action, Val, A]
  }

  case class IncompleteImpl[Action[_, _], Val[_], X, Y, A](
    input: Input[Val, X],
    cont: Closure[Action, Val, X, Y],
    resultAcc: Capture[**, Value[Val, _], Y, A],
  ) extends Incomplete[Action, Val, A] {
    override def isReducible: Boolean =
      input.isPartiallyReady

    override def crank(using Unzippable[**, Val]): CrankRes[Action, Val, A] =
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

  enum PartiallyApplied[Action[_, _], Val[_], A, B]:
    case DomainAction[Action[_, _], Val[_], A, X, B](
      args: Capture[**, Value[Val, _], A, X],
      f: Action[X, B],
    ) extends PartiallyApplied[Action, Val, A, B]
    case DistLR[Action[_, _], Val[_], X, Y, Z](
      x: Value[Val, X],
    ) extends PartiallyApplied[Action, Val, Y ++ Z, (X ** Y) ++ (X ** Z)]

  object PartiallyApplied {
    def action[Action[_, _], Val[_], A, B](f: Action[A, B]): PartiallyApplied[Action, Val, A, B] =
      PartiallyApplied.DomainAction(Capture.NoCapture(), f)
  }

  type Closure[Action[_, _], Val[_], A, B] =
    FlowAST[PartiallyApplied[Action, Val, _, _], A, B]

  object Closure {
    type Work[Action[_, _], Val[_], A, B] =
      FlowAST.Work[PartiallyApplied[Action, Val, _, _], A, B]

    type Shuffled[Action[_, _], Val[_]] =
      libretto.lambda.Shuffled[Work[Action, Val, _, _], **]

    def ssc[Action[_, _], Val[_]] =
      summon[libretto.lambda.SymmetricSemigroupalCategory[Closure[Action, Val, _, _], **]]

    def shuffled[Action[_, _], Val[_]]: Shuffled[Action, Val] =
      FlowAST.shuffled

    def fromShuffled[Action[_, _], Val[_], A, B](using sh: Shuffled[Action, Val])(
      f: sh.Shuffled[A, B],
    ): Closure[Action, Val, A, B] =
      FlowAST.fromShuffled(f)

    def pure[Action[_, _], Val[_], A, B](f: FlowAST[Action, A, B]): Closure[Action, Val, A, B] =
      f.translate([x, y] => (g: Action[x, y]) => PartiallyApplied.action[Action, Val, x, y](g))

    def distLR[Action[_, _], Val[_], A, B, C](captured: Value[Val, A]): Closure[Action, Val, B ++ C, (A ** B) ++ (A ** C)] =
      FlowAST.DomainAction(PartiallyApplied.DistLR(captured))

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

    def partiallyAppliedAction[Action[_, _], Val[_], A, X, B](
      args: Capture[**, Value[Val, _], A, X],
      f: Action[X, B],
    ): Closure.Work[Action, Val, A, B] =
      FlowAST.DomainAction(
        PartiallyApplied.DomainAction(args, f),
      )
  }

  def init[Action[_, _], Val[_], A, B](
    input: Value[Val, A],
    wf: FlowAST[Action, A, B],
  ): WorkflowInProgress[Action, Val, B] =
    IncompleteImpl(
      Input.Ready(input),
      Closure.pure(wf),
      Capture.NoCapture(),
    )

  private def propagateValue[Action[_, _], Val[_], F[_], A, B, C](
    value: Value[Val, A],
    remainingInput: Spine[**, Input[Val, _], F],
    cont: Closure[Action, Val, F[A], B],
    resultAcc: Capture[**, Value[Val, _], B, C],
  )(using
    Unzippable[**, Val],
  ): CrankRes[Action, Val, C] = {
    given sh: Closure.Shuffled[Action, Val] =
      Closure.shuffled[Action, Val]

    import sh.ChaseFwRes.*

    cont.toShuffled.chaseFw(remainingInput.focus) match
      case Transported(s, ev) =>
        accumulateResult(value, resultAcc.from(using ev), remainingInput, s)
      case Split(ev1) =>
        // split value and continue with a half
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case r: FedTo[f, a, v, w, g, b] =>
        def go[V[_], G[_], W](
          pre: sh.Punched[F, [x] =>> G[V[x]]],
          v: Focus[**, V],
          f: Closure.Work[Action, Val, V[A], W],
          g: Focus[**, G],
          post: sh.Shuffled[G[W], B],
        ): CrankRes[Action, Val, C] =
          f.maskInput.visit { [VA] => (f: Closure.Work[Action, Val, VA, W], ev: VA =:= V[A]) => f match
            case FlowAST.Dup() =>
              ev match { case TypeEq(Refl()) =>
                v match
                  case Focus.Id() =>
                    val i = Input.Ready(value)
                    val input = remainingInput.plugFold(i ** i)
                    val pre1  = pre.plug[A ** A]
                    val cont1 = Closure.fromShuffled(pre1 > post)
                    CrankRes.Progressed(IncompleteImpl(input, cont1, resultAcc))
                  case Focus.Fst(i) =>
                    throw NotImplementedError(s"at ${summon[SourcePos]}")
                  case Focus.Snd(i) =>
                    throw NotImplementedError(s"at ${summon[SourcePos]}")
              }

            case f1: FlowAST.DistributeLR[op, x, y, z] =>
              summon[VA =:= (x ** (y ++ z))]
              v match
                case v: Focus.Fst[p, v1, yz] =>
                  (summon[(x ** (y ++ z)) =:= VA] andThen ev andThen summon[V[A] =:= (v1[A] ** yz)]) match
                    case BiInjective[**](TypeEq(Refl()), TypeEq(Refl())) =>
                      distributePartLR[v1, y, z, G](pre, v.i, post, g)
                case Focus.Snd(i) =>
                  throw NotImplementedError(s"DistributeLR() at $v (at ${summon[SourcePos]})")
                case Focus.Id() =>
                  throw NotImplementedError(s"DistributeLR() at $v (at ${summon[SourcePos]})")

            case FlowAST.IntroFst() =>
              v match
                case Focus.Id() =>
                  ev match { case TypeEq(Refl()) =>
                    summon[W =:= (Unit ** A)]
                    val input = remainingInput.plugFold(Input.Ready(Value.unit) ** Input.Ready(value))
                    CrankRes.Progressed(IncompleteImpl(input, Closure.fromShuffled(pre[Unit ** A] > post), resultAcc))
                  }
                case Focus.Fst(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")
                case Focus.Snd(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")

            case _: FlowAST.Promise[op, x] =>
              v match
                case Focus.Id() =>
                  summon[W =:= (PromiseRef[x] ** x)]
                  CrankRes.Ask { (px: PromiseId[x]) =>
                    val input = remainingInput.plugFold(Input.Ready(Value.promiseRef(px)) ** Input.awaiting(px))
                    IncompleteImpl(input, Closure.fromShuffled(pre[PromiseRef[x] ** x] > post), resultAcc)
                  }
                case Focus.Fst(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")
                case Focus.Snd(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")

            case _: FlowAST.PromiseMake[op, x] =>
              v match
                case Focus.Id() =>
                  summon[W =:= (Due[x] ** Promised[x])]
                  CrankRes.Ask { (px: PromiseId[x]) =>
                    val input = remainingInput.plugFold(Input.Ready(Value.duePromise(px)) ** Input.promised(px))
                    IncompleteImpl(input, Closure.fromShuffled(pre[Due[x] ** Promised[x]] > post), resultAcc)
                  }
                case Focus.Fst(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")
                case Focus.Snd(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")

            case FlowAST.DomainAction(action) =>
              action match
                case PartiallyApplied.DomainAction(partialArgs, action) =>
                  ev match { case TypeEq(Refl()) =>
                    v match
                      case Focus.Id() =>
                        val args = partialArgs.complete(value).fold
                        CrankRes.ActionRequest(
                          args,
                          action,
                          px => IncompleteImpl(
                            remainingInput.plugFold(Input.awaiting(px)),
                            Closure.fromShuffled(pre[W] > post),
                            resultAcc,
                          ),
                        )
                      case v: Focus.Proper[prod, f] =>
                          partialArgs.absorb(value, v) match
                            case Capture.Absorbed.Impl(k, r) =>
                              val k1 = k.at(g)
                              pre.knitBw(k1) match
                                case Exists.Some((k0, pre1)) =>
                                  val input = remainingInput.knitFold(k0)
                                  val f1 = sh.lift(Closure.partiallyAppliedAction(r, action)).at(g)
                                  val cont1 = Closure.fromShuffled(pre1 > f1 > post)
                                  CrankRes.Progressed(IncompleteImpl(input, cont1, resultAcc))
                  }
                case PartiallyApplied.DistLR(x) =>
                  UnhandledCase.raise(s"propagateValue into $action at $v")

            case other =>
              UnhandledCase.raise(s"propagateValue $value into $other at $v")
          }

        def distributePartLR[V[_], Y, Z, G[_]](
          // value: Value[Val, A],
          // remainingInput: Spine[**, Input[Val, _], F],
          pre: sh.Punched[F, [a] =>> G[V[a] ** (Y ++ Z)]],
          v: Focus[**, V],
          post: sh.Shuffled[G[(V[A] ** Y) ++ (V[A] ** Z)], B],
          g: Focus[**, G],
          // resultAcc: Capture[**, Value[Val, _], B, C],
        ): CrankRes[Action, Val, C] =
          v match
            case Focus.Id() =>
              summon[V[A] =:= A]
              val k: Knitted[**, [a] =>> G[a ** (Y ++ Z)], G[Y ++ Z]] =
                Knitted.keepSnd[**, Y ++ Z].at[G](g)
              pre.knitBw(k) match
                case Exists.Some((k, f)) =>
                  val input = remainingInput.knitFold(k)
                  val op = Closure.distLR[Action, Val, A, Y, Z](value)
                  val post1 = op.toShuffled.at(g) > post
                  CrankRes.Progressed(IncompleteImpl(input, Closure.fromShuffled(f > post1), resultAcc))
            case other =>
              throw NotImplementedError(s"$other (at ${summon[SourcePos]})")

        go[v, g, w](r.pre, r.v, r.f, r.g, r.post)
  }

  private def accumulateResult[Action[_, _], Val[_], F[_], G[_], A, B](using
    sh: Closure.Shuffled[Action, Val],
  )(
    newResult: Value[Val, A],
    resultAcc: Capture[**, Value[Val, _], G[A], B],
    remainingInput: Spine[**, Input[Val, _], F],
    cont: sh.Punched[F, G],
  ): CrankRes[Action, Val, B] =
    // feed `value` into `resultAcc`
    throw NotImplementedError(s"at ${summon[SourcePos]}")

  enum CrankRes[Action[_, _], Val[_], A]:
    case AlreadyStuck(w: WorkflowInProgress.Incomplete[Action, Val, A])
    case Progressed(w: WorkflowInProgress[Action, Val, A])
    case Ask[Action[_, _], Val[_], X, A](
      cont: PromiseId[X] => WorkflowInProgress[Action, Val, A],
    ) extends CrankRes[Action, Val, A]
    case ActionRequest[Action[_, _], Val[_], X, Y, A](
      input: Value[Val, X],
      action: Action[X, Y],
      cont: PromiseId[Y] => WorkflowInProgress[Action, Val, A],
    ) extends CrankRes[Action, Val, A]
}
