package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{Capture, Focus, Knit, Knitted, Spine, SymmetricSemigroupalCategory, UnhandledCase, Unzippable}
import libretto.lambda.examples.workflow.generic.lang.{**, ++, FlowAST, InputPortRef, Reading, given}
import libretto.lambda.util.{BiInjective, Exists, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl

object RuntimeFlows {
  opaque type Flow[Op[_, _], Val[_], A, B] =
    FlowAST[RuntimeAction[Op, Val, _, _], A, B]

  def ssc[Op[_, _], Val[_]] =
    summon[SymmetricSemigroupalCategory[Flow[Op, Val, _, _], **]]

  def pure[Op[_, _], Val[_], A, B](f: FlowAST[Op, A, B]): Flow[Op, Val, A, B] =
    f.translate([x, y] => (g: Op[x, y]) => RuntimeAction.action[Op, Val, x, y](g))

  def distLR[Op[_, _], Val[_], A, B, C](captured: Value[Val, A]): Flow[Op, Val, B ++ C, (A ** B) ++ (A ** C)] =
    FlowAST.DomainAction(RuntimeAction.DistLR(captured))

  def id[Op[_, _], Val[_], A]: Flow[Op, Val, A, A] =
    FlowAST.Id()

  def swap[Op[_, _], Val[_], A, B]: Flow[Op, Val, A ** B, B ** A] =
    FlowAST.Swap()

  def assocLR[Op[_, _], Val[_], A, B, C]: Flow[Op, Val, (A ** B) ** C, A ** (B ** C)] =
    FlowAST.AssocLR()

  def assocRL[Op[_, _], Val[_], A, B, C]: Flow[Op, Val, A ** (B ** C), (A ** B) ** C] =
    FlowAST.AssocRL()

  def fst[Op[_, _], Val[_], A, B, Y](f: Flow[Op, Val, A, B]): Flow[Op, Val, A ** Y, B ** Y] =
    ssc.fst(f)

  def snd[Op[_, _], Val[_], A, B, X](f: Flow[Op, Val, A, B]): Flow[Op, Val, X ** A, X ** B] =
    ssc.snd(f)

  def dup[Op[_, _], Val[_], A]: Flow[Op, Val, A, A ** A] =
    FlowAST.Dup()

  def action[Op[_, _], Val[_], A, B](f: RuntimeAction[Op, Val, A, B]): Flow[Op, Val, A, B] =
    FlowAST.DomainAction(f)

  private type Work[Action[_, _], Val[_], A, B] =
    FlowAST.Work[RuntimeAction[Action, Val, _, _], A, B]

  private type Shuffled[Action[_, _], Val[_]] =
    libretto.lambda.Shuffled[Work[Action, Val, _, _], **]

  private def shuffled[Action[_, _], Val[_]]: Shuffled[Action, Val] =
    FlowAST.shuffled

  private def fromShuffled[Action[_, _], Val[_], A, B](using sh: Shuffled[Action, Val])(
    f: sh.Shuffled[A, B],
  ): Flow[Action, Val, A, B] =
    FlowAST.fromShuffled(f)

  private def toShuffled[Action[_, _], Val[_], A, B](
    f: Flow[Action, Val, A, B],
  )(using
    sh: Shuffled[Action, Val],
  ): sh.Shuffled[A, B] =
    f.toShuffled(using sh)

  def propagateValue[Action[_, _], Val[_], F[_], A, B](
    value: Value[Val, A],
    F: Focus[**, F],
    cont: Flow[Action, Val, F[A], B],
  )(using
    Unzippable[**, Val],
  ): PropagateValueRes[Action, Val, F, B] = {
    given sh: Shuffled[Action, Val] =
      RuntimeFlows.shuffled[Action, Val]

    import sh.ChaseFwRes.*

    cont.toShuffled.chaseFw(F) match
      case Transported(s, ev) =>
        PropagateValueRes.Transported.Impl(s, ev, value)
      case Split(ev1) =>
        // split value and continue with a half
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case r: FedTo[f, a, v, w, g, b] =>
        def go[V[_], G[_], W](
          pre: sh.Punched[F, [x] =>> G[V[x]]],
          v: Focus[**, V],
          f: Work[Action, Val, V[A], W],
          g: Focus[**, G],
          post: sh.Shuffled[G[W], B],
        ): PropagateValueRes[Action, Val, F, B] =
          f.maskInput.visit { [VA] => (f: Work[Action, Val, VA, W], ev: VA =:= V[A]) => f match
            case FlowAST.Dup() =>
              ev match { case TypeEq(Refl()) =>
                v match
                  case Focus.Id() =>
                    val i = Input.Ready(value)
                    val cont1 = fromShuffled(pre.plug[A ** A] > post)
                    PropagateValueRes.Transformed(i ** i, cont1)
                  case Focus.Fst(i) =>
                    UnhandledCase.raise(s"propagateValue into $f at $v")
                  case Focus.Snd(i) =>
                    UnhandledCase.raise(s"propagateValue into $f at $v")
              }

            case f1: FlowAST.DistributeLR[op, x, y, z] =>
              summon[VA =:= (x ** (y ++ z))]
              v match
                case v: Focus.Fst[p, v1, yz] =>
                  (summon[(x ** (y ++ z)) =:= VA] andThen ev andThen summon[V[A] =:= (v1[A] ** yz)]) match
                    case BiInjective[**](TypeEq(Refl()), TypeEq(Refl())) =>
                      distributePartLR[v1, y, z, G](pre, v.i, post, g)
                case Focus.Snd(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")
                case Focus.Id() =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")

            case FlowAST.IntroFst() =>
              v match
                case Focus.Id() =>
                  ev match { case TypeEq(Refl()) =>
                    summon[W =:= (Unit ** A)]
                    val input = Input.Ready(Value.unit) ** Input.Ready(value)
                    PropagateValueRes.Transformed(input, fromShuffled(pre[Unit ** A] > post))
                  }
                case Focus.Fst(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")
                case Focus.Snd(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")

            case _: FlowAST.Read[op, x] =>
              v match
                case Focus.Id() =>
                  summon[W =:= (InputPortRef[x] ** Reading[x])]
                  PropagateValueRes.Read(fromShuffled(pre[InputPortRef[x] ** Reading[x]] > post))
                case Focus.Fst(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")
                case Focus.Snd(i) =>
                  UnhandledCase.raise(s"propagateValue into $f at $v")

            case FlowAST.DomainAction(action) =>
              action match
                case RuntimeAction.DomainAction(partialArgs, action) =>
                  ev match { case TypeEq(Refl()) =>
                    v match
                      case Focus.Id() =>
                        val args = partialArgs.complete(value).fold
                        PropagateValueRes.ActionRequest(
                          args,
                          action,
                          fromShuffled(pre[W] > post),
                        )
                      case v: Focus.Proper[prod, f] =>
                        partialArgs.absorb(value, v) match
                          case Capture.Absorbed.Impl(k, r) =>
                            val k1 = k.at(g)
                            pre.knitBw(k1) match
                              case Exists.Some((k0, pre1)) =>
                                // val input = remainingInput.knitFold(k0)
                                val f1 = toShuffled(RuntimeFlows.action(RuntimeAction.partiallyApplied(r, action))).at(g)
                                val cont1 = fromShuffled(pre1 > f1 > post)
                                // CrankRes.Progressed(IncompleteImpl(input, cont1, resultAcc))
                                PropagateValueRes.Absorbed(k0, cont1)
                  }
                case RuntimeAction.DistLR(x) =>
                  UnhandledCase.raise(s"propagateValue into $action at $v")

            case FlowAST.DoWhile(body) =>
              ev match { case TypeEq(Refl()) =>
                val f1 = body >>> FlowAST.Either(FlowAST.DoWhile(body), FlowAST.Id())
                val cont = fromShuffled(pre[A] > toShuffled(f1).at(g) > post)
                PropagateValueRes.Transformed[Action, Val, F, A, B](Input.Ready(value), cont)
              }
            case other =>
              UnhandledCase.raise(s"propagateValue $value into $other at $v")
          }

        def distributePartLR[V[_], Y, Z, G[_]](
          pre: sh.Punched[F, [a] =>> G[V[a] ** (Y ++ Z)]],
          v: Focus[**, V],
          post: sh.Shuffled[G[(V[A] ** Y) ++ (V[A] ** Z)], B],
          g: Focus[**, G],
        ): PropagateValueRes[Action, Val, F, B] =
          v match
            case Focus.Id() =>
              summon[V[A] =:= A]
              val k: Knitted[**, [a] =>> G[a ** (Y ++ Z)], G[Y ++ Z]] =
                Knitted.keepSnd[**, Y ++ Z].at[G](g)
              pre.knitBw(k) match
                case Exists.Some((k, f)) =>
                  val op = RuntimeFlows.distLR[Action, Val, A, Y, Z](value)
                  val post1 = toShuffled(op).at(g) > post
                  PropagateValueRes.Absorbed(k, fromShuffled(f > post1))
            case other =>
              UnhandledCase.raise(s"distributePartLR at $other")

        go[v, g, w](r.pre, r.v, r.f, r.g, r.post)
  }

  sealed trait PropagateValueRes[Action[_, _], Val[_], F[_], B]

  object PropagateValueRes {
    sealed trait Transported[Action[_, _], Val[_], F[_], B]
      extends PropagateValueRes[Action, Val, F, B]
    object Transported {
      class Impl[Action[_, _], Val[_], F[_], X, G[_], B](using sh: Shuffled[Action, Val])(
        f: sh.Punched[F, G],
        ev: G[X] =:= B,
        value: Value[Val, X],
      ) extends Transported[Action, Val, F, B]
    }

    case class Transformed[Action[_, _], Val[_], F[_], Y, B](
      newInput: Input[Val, Y],
      f: Flow[Action, Val, F[Y], B],
    ) extends PropagateValueRes[Action, Val, F, B]

    case class Absorbed[Action[_, _], Val[_], F[_], F0, B](
      k: Knitted[**, F, F0],
      f: Flow[Action, Val, F0, B],
    ) extends PropagateValueRes[Action, Val, F, B]

    case class Read[Action[_, _], Val[_], F[_], Y, B](
      cont: Flow[Action, Val, F[InputPortRef[Y] ** Reading[Y]], B]
    ) extends PropagateValueRes[Action, Val, F, B]

    case class ActionRequest[Action[_, _], Val[_], F[_], X, Y, B](
      input: Value[Val, X],
      action: Action[X, Y],
      cont: Flow[Action, Val, F[Y], B],
    ) extends PropagateValueRes[Action, Val, F, B]
  }
}
