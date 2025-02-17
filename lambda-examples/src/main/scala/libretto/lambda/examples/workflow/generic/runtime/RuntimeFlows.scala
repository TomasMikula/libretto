package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{Capture, DistributionNAry, EnumModule, Focus, Knit, Knitted, ParN, Projection, Spine, SymmetricSemigroupalCategory, UnhandledCase, Unzippable}
import libretto.lambda.examples.workflow.generic.lang.{**, ++, ||, ::, Enum, FlowAST, PortName, Reading, given}
import libretto.lambda.util.{BiInjective, Exists, SourcePos, TypeEq, TypeEqK}
import libretto.lambda.util.TypeEq.Refl
import scala.concurrent.duration.FiniteDuration

object RuntimeFlows {
  opaque type Flow[Op[_, _], Val[_], A, B] =
    FlowAST[RuntimeAction[Op, Val, _, _], A, B]

  def ssc[Op[_, _], Val[_]] =
    summon[SymmetricSemigroupalCategory[Flow[Op, Val, _, _], **]]

  def pure[Op[_, _], Val[_], A, B](f: FlowAST[Op, A, B]): Flow[Op, Val, A, B] =
    f.translate([x, y] => (g: Op[x, y]) => RuntimeAction.action[Op, Val, x, y](g))

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

  def inl[Op[_, _], Val[_], A, B]: Flow[Op, Val, A, A ++ B] =
    FlowAST.injectL

  def inr[Op[_, _], Val[_], A, B]: Flow[Op, Val, B, A ++ B] =
    FlowAST.injectR

  def either[Op[_, _], Val[_], A, B, C](
    f: Flow[Op, Val, A, C],
    g: Flow[Op, Val, B, C],
  ): Flow[Op, Val, A ++ B, C] =
    FlowAST.either(f, g)

  def eitherBimap[Op[_, _], Val[_], A, B, C, D](
    f: Flow[Op, Val, A, C],
    g: Flow[Op, Val, B, D],
  ): Flow[Op, Val, A ++ B, C ++ D] =
    either(f >>> inl, g >>> inr)

  private def enumModule[Op[_, _], Val[_]]: EnumModule[Flow[Op, Val, _, _], **, Enum, ||, ::] =
    FlowAST.enumModule[RuntimeAction[Op, Val, _, _]]

  def enumMap[Op[_, _], Val[_], As, Bs](
    fs: ParN.Named[||, ::, Flow[Op, Val, _, _], As, Bs],
  ): Flow[Op, Val, Enum[As], Enum[Bs]] =
    enumModule[Op, Val].nmap(fs)

  def distributeLR[Op[_, _], Val[_], A, B, C]: Flow[Op, Val, A ** (B ++ C), (A ** B) ++ (A ** C)] =
    FlowAST.distributeLR

  def action[Op[_, _], Val[_], A, B](f: RuntimeAction[Op, Val, A, B]): Flow[Op, Val, A, B] =
    FlowAST.Ext(f)

  def distLRNAry[Op[_, _], Val[_], A, Cases, ACases](
    captured: Value[Val, A],
    d: DistributionNAry.DistLR[**, ||, ::, A, Cases] { type Out = ACases },
  ): Flow[Op, Val, Enum[Cases], Enum[ACases]] =
    action(RuntimeAction.DistLRNAry(captured, d))

  extension [Op[_, _], Val[_], A, B](flow: Flow[Op, Val, A, B])
    def >>>[C](that: Flow[Op, Val, B, C]): Flow[Op, Val, A, C] =
      FlowAST.AndThen(flow, that)

  private type Work[Action[_, _], Val[_], A, B] =
    FlowAST.Work[RuntimeAction[Action, Val, _, _], A, B]

  private type Shuffled[Action[_, _], Val[_]] =
    libretto.lambda.ShuffledModule[Work[Action, Val, _, _], **]

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
    Value.Compliant[Val],
  ): PropagateValueRes[Action, Val, F, B] = {
    given sh: Shuffled[Action, Val] =
      RuntimeFlows.shuffled[Action, Val]

    import sh.ChaseFwRes.*

    cont.toShuffled.chaseFw(F) match
      case tr: Transported[f, a, g, b] =>
        summon[a =:= A]
        summon[b =:= B]
        summon[f[a] =:= F[A]]
        given (g[A] =:= B) = tr.ev
        tr.s.focusOut match
          case Focus.Id() =>
            sh.Punched.proveIdBw(tr.s) match
              case TypeEqK.Refl() =>
                PropagateValueRes.Complete(value.as[B])
          case p: Focus.Proper[pr, g] =>
            // Note: If in the future we call propagateValue recursively,
            // make sure value collector is introduced only at the output of the whole workflow
            // and not in the middle, as it would introduce an uncolicited synchronization point.
            RuntimeAction.captureValue[Action, Val, g, A](value, p) match
              case Exists.Some((collector, k)) =>
                tr.s.knitBw(k) match
                  case Exists.Some((k1, s1)) =>
                    PropagateValueRes.Absorbed(k1, fromShuffled(s1) >>> action(collector).to[B])
      case Split(ev) =>
        val (a1, a2) = Value.unpair(ev.substituteCo(value))
        val input = ev.substituteContra(Input.Ready(a1) ** Input.Ready(a2))
        PropagateValueRes.Transformed(input, cont)
      case r: FedTo[f, a, v, w, g, b] =>
        feedValue[Action, Val, F, v, A, g, w, B](value, r.pre, r.v, r.f, r.g, r.post)
  }

  private def feedValue[Action[_, _], Val[_], F[_], V[_], A, G[_], W, B](using sh: Shuffled[Action, Val])(
    value: Value[Val, A],
    pre: sh.Punched[F, [x] =>> G[V[x]]],
    v: Focus[**, V],
    f: Work[Action, Val, V[A], W],
    g: Focus[**, G],
    post: sh.Shuffled[G[W], B],
  )(using
    Value.Compliant[Val],
  ): PropagateValueRes[Action, Val, F, B] =
    feedValue[Action, Val, V, A, W](value, v, f) match {
      case FeedValueRes.Complete(result) =>
        PropagateValueRes.Transformed(result, fromShuffled(pre.plug[W] > post))
      case FeedValueRes.Transformed(newInput, cont) =>
        PropagateValueRes.Transformed(newInput, fromShuffled(pre.plug > toShuffled(cont).at(g) > post))
      case FeedValueRes.Absorbed(k, cont) =>
        pre.knitBw(k.at(g)) match
          case Exists.Some((k1, pre1)) =>
            PropagateValueRes.Absorbed(k1, fromShuffled(pre1 > toShuffled(cont).at(g) > post))
      case FeedValueRes.Shrunk(newInput, p) =>
        project(pre.plug, p.at(g)) match
          case sh.ProjectRes.Projected(p0, pre1) =>
            PropagateValueRes.Shrunk(newInput, p0, fromShuffled(pre1 > post))
      case _: FeedValueRes.Read[act, vl, x] =>
        PropagateValueRes.Read(fromShuffled(pre.plug[PortName[x] ** Reading[x]] > post))
      case FeedValueRes.ReadAwaitTimeout(toAwait, timeout) =>
        PropagateValueRes.ReadAwaitTimeout(toAwait, timeout, fromShuffled(pre.plug > post))
      case FeedValueRes.ActionRequest(input, action) =>
        PropagateValueRes.ActionRequest(input, action, fromShuffled(pre.plug > post))
    }

  private def feedValue[Action[_, _], Val[_], V[_], A, W](using sh: Shuffled[Action, Val])(
    value: Value[Val, A],
    v: Focus[**, V],
    f: Work[Action, Val, V[A], W],
  )(using
    Value.Compliant[Val],
  ): FeedValueRes[Action, Val, V, W] =
    f.maskInput.visit[FeedValueRes[Action, Val, V, W]] { [VA] => (f: Work[Action, Val, VA, W], ev: VA =:= V[A]) => f match
      case FlowAST.Dup() =>
        ev match { case TypeEq(Refl()) =>
          v match
            case Focus.Id() =>
              val i = Input.Ready(value)
              FeedValueRes.Complete(i ** i)
            case Focus.Fst(i) =>
              UnhandledCase.raise(s"propagateValue into $f at $v")
            case Focus.Snd(i) =>
              UnhandledCase.raise(s"propagateValue into $f at $v")
        }

      case _: FlowAST.Prj1[op, x, y] =>
        summon[VA =:= (x ** y)]
        summon[W =:= x]
        FeedValueRes.Shrunk(
          Input.Ready(value),
          Projection.discardSnd[**, x, y].from(using ev.flip)
        )

      case _: FlowAST.Prj2[op, x, y] =>
        summon[VA =:= (x ** y)]
        summon[W =:= y]
        FeedValueRes.Shrunk(
          Input.Ready(value),
          Projection.discardFst[**, x, y].from(using ev.flip)
        )

      case i: FlowAST.Inject[op, lbl, a, cases] =>
        summon[VA =:= a]
        summon[W =:= Enum[cases]]
        given (V[A] =:= a) = ev.flip
        v match
          case Focus.Id() =>
            summon[V[A] =:= A]
            val result = Input.Ready(Value.ofEnum(i.i, value.as[VA]))
            FeedValueRes.Complete(result)
          case v: Focus.Proper[**, V] =>
            collectingInput(value, v, i.from[V[A]])

      case h: FlowAST.Handle[op, cases, w] =>
        summon[VA =:= Enum[cases]]
        summon[W =:= w]
        v match
          case Focus.Id() =>
            val enumValue: Value[Val, Enum[cases]] = value.as[Enum[cases]](using ev.flip)
            Value.revealCase(enumValue) match
              case Exists.Some(Exists.Some(inj)) =>
                val handler = h.handlers.get(inj.i)
                FeedValueRes.Transformed(Input.Ready(inj.a), handler)
          case other =>
            throw AssertionError(s"Impossible: would mean that `Enum` = `**`, which is impossible if they are different class types.")

      case d: FlowAST.DistributeNAryLR[op, x, cases, xcases] =>
        summon[VA =:= (x ** Enum[cases])]
        summon[W =:= Enum[xcases]]
        v match
          case v: Focus.Fst[p, v1, enm] =>
            (summon[(x ** Enum[cases]) =:= VA] andThen ev andThen summon[V[A] =:= (v1[A] ** enm)]) match
              case BiInjective[**](TypeEq(Refl()), TypeEq(Refl())) =>
                summon[enm =:= Enum[cases]]
                feedDistributeeNAryLR[Action, Val, v1, A, cases, xcases](value, v.i, d.dist)
          case Focus.Snd(_) =>
            UnhandledCase.raise(s"propagateValue into $f at $v")
          case Focus.Id() =>
            UnhandledCase.raise(s"propagateValue into $f at $v")

      case FlowAST.IntroFst() =>
        v match
          case Focus.Id() =>
            ev match { case TypeEq(Refl()) =>
              summon[W =:= (Unit ** A)]
              val input = Input.Ready(Value.unit) ** Input.Ready(value)
              FeedValueRes.Complete(input)
            }
          case Focus.Fst(i) =>
            UnhandledCase.raise(s"propagateValue into $f at $v")
          case Focus.Snd(i) =>
            UnhandledCase.raise(s"propagateValue into $f at $v")

      case _: FlowAST.Read[op, x] =>
        summon[VA =:= Unit]
        v match
          case Focus.Id() =>
            summon[W =:= (PortName[x] ** Reading[x])]
            FeedValueRes.Read[Action, Val, x]()
          case Focus.Fst(_) | Focus.Snd(_) =>
            throw AssertionError(s"Impossible: would mean that `Unit` = `a ** b`")

      case FlowAST.DoWhile(body) =>
        ev match { case TypeEq(Refl()) =>
          val f1 = body >>> FlowAST.either(FlowAST.DoWhile(body), FlowAST.Id())
          FeedValueRes.Transformed(Input.Ready(value), f1)
        }

      case read: FlowAST.ReadAwait[op, a] =>
        v match
          case Focus.Id() =>
            given (A =:= Reading[a]) =
              summon[A =:= V[A]] andThen ev.flip andThen summon[VA =:= Reading[a]]
            val ref =
              Value.extractPortId(value.as[Reading[a]])
            FeedValueRes.Complete(Input.awaitingInput(ref))
          case other =>
            throw AssertionError(s"Impossible: would mean that `Reading[a]` = `x ** y`")

      case read: FlowAST.ReadAwaitTimeout[op, a] =>
        v match
          case Focus.Id() =>
            val ev1: Reading[a] =:= A =
              summon[Reading[a] =:= VA] andThen ev
            val awaited: Value[Val, Reading[a]] =
              ev1.substituteContra[Value[Val, _]](value)
            FeedValueRes.ReadAwaitTimeout[Action, Val, a](awaited, read.duration)
          case other =>
            throw AssertionError(s"Impossible: would mean that `Reading[a]` = `x ** y`")

      case FlowAST.Ext(action) =>
        action match
          case a @ RuntimeAction.DomainAction(action) =>
            ev match { case TypeEq(Refl()) =>
              v match
                case Focus.Id() =>
                  FeedValueRes.ActionRequest(value, action)
                case v: Focus.Proper[prod, v] =>
                  collectingInput(value, v, RuntimeFlows.action(a))
            }

          case d: RuntimeAction.DistLRNAry[op, val_, x, cases, xCases] =>
            summon[VA =:= Enum[cases]]
            summon[W =:= Enum[xCases]]
            v match
              case Focus.Id() =>
                (summon[Enum[cases] =:= VA] andThen ev andThen summon[V[A] =:= A]) match
                  case TypeEq(Refl()) =>
                    val res: Value[Val, Enum[xCases]] =
                      Value.distLRNAry[Val, x, cases, xCases](d.a, value, d.d)
                    FeedValueRes.Complete(Input.Ready(res))
              case other =>
                throw AssertionError(s"Impossible, would mean that `Enum` = `**`")

          case RuntimeAction.ValueCollector(f) =>
            v match
              case Focus.Id() =>
                val res: Value[Val, W] = f.complete(ev.substituteContra(value)).fold
                FeedValueRes.Complete(Input.Ready(res))
              case v: Focus.Proper[**, V] =>
                given (V[A] =:= VA) = ev.flip
                f.absorb[V, A](value, v) match
                  case Capture.Absorbed.Impl(k, f1) =>
                    FeedValueRes.Absorbed(k, RuntimeFlows.action(RuntimeAction.ValueCollector(f1)))

      case other =>
        UnhandledCase.raise(s"propagateValue $value into $other at $v")
    }

  private def collectingInput[Action[_, _], Val[_], V[_], A, W](
    a: Value[Val, A],
    v: Focus.Proper[**, V],
    cont: Flow[Action, Val, V[A], W],
  ): FeedValueRes[Action, Val, V, W] =
    RuntimeAction.captureValue[Action, Val, V, A](a, v) match
      case Exists.Some((collector, k)) =>
        FeedValueRes.Absorbed(k, action(collector) >>> cont)

  private def feedDistributeeNAryLR[Action[_, _], Val[_], V[_], A, Cases, VACases](
    value: Value[Val, A],
    v: Focus[**, V],
    d: DistributionNAry.DistLR[**, ||, ::, V[A], Cases] { type Out = VACases },
  ): FeedValueRes[Action, Val, [a] =>> V[a] ** Enum[Cases], Enum[VACases]] =
    v match
      case Focus.Id() =>
        summon[V[A] =:= A]
        val k: Knitted[**, [a] =>> a ** Enum[Cases], Enum[Cases]] =
          Knitted.keepSnd[**, Enum[Cases]]
        val op = RuntimeFlows.distLRNAry[Action, Val, A, Cases, VACases](value, d)
        FeedValueRes.Absorbed(k, op)
      case v: Focus.Proper[pr, v] =>
        val ev = v.provePair[A]
        type P = ev.T
        type Q = ev.value.T
        given ev1: (V[A] =:= (P ** Q)) =
          ev.value.value
        d.separately[P, Q] match
          case Exists.Some(Exists.Some((dq, dp, assocs))) =>
            val distSeparately =
              fst(id[Action, Val, V[A]].to[P ** Q])
              >>> assocLR[Action, Val, P, Q, Enum[Cases]]
              >>> snd(FlowAST.DistributeNAryLR(dq))
              >>> FlowAST.DistributeNAryLR(dp)
              >>> enumMap(assocs.translate(
                [X, Y] => (f: Exists[[b] =>> (X =:= (P ** (Q ** b)), ((P ** Q) ** b) =:= Y)]) =>
                  f match {
                    case e @ Exists.Some((TypeEq(Refl()), TypeEq(Refl()))) =>
                      assocRL[Action, Val, P, Q, e.T]
                  }
              ))
            FeedValueRes.Transformed(Input.Ready(value), distSeparately)

  private def project[Action[_, _], Val[_], A, B, C](using sh: Shuffled[Action, Val])(
    f: sh.Shuffled[A, B],
    p: Projection[**, B, C],
  ): sh.ProjectRes[A, C] =
    f.project(
      p,
      [X, Y, Z] => (w: Work[Action, Val, X, Y], p: Projection[**, Y, Z]) => {
        UnhandledCase.raise(s"Projecting $w by $p")
      },
    )

  sealed trait PropagateValueRes[Action[_, _], Val[_], F[_], B]

  object PropagateValueRes {
    case class Complete[Action[_, _], Val[_], B](
      result: Value[Val, B],
    ) extends PropagateValueRes[Action, Val, [x] =>> x, B]

    case class Transformed[Action[_, _], Val[_], F[_], Y, B](
      newInput: Input[Val, Y],
      f: Flow[Action, Val, F[Y], B],
    ) extends PropagateValueRes[Action, Val, F, B]

    case class Absorbed[Action[_, _], Val[_], F[_], F0, B](
      k: Knitted[**, F, F0],
      f: Flow[Action, Val, F0, B],
    ) extends PropagateValueRes[Action, Val, F, B]

    case class Shrunk[Action[_, _], Val[_], F[_], X, F0, B](
      newValue: Input[Val, X],
      p: Projection[**, F[X], F0],
      f: Flow[Action, Val, F0, B],
    ) extends PropagateValueRes[Action, Val, F, B]

    case class Read[Action[_, _], Val[_], F[_], Y, B](
      cont: Flow[Action, Val, F[PortName[Y] ** Reading[Y]], B]
    ) extends PropagateValueRes[Action, Val, F, B]

    case class ReadAwaitTimeout[Action[_, _], Val[_], F[_], Y, B](
      toAwait: Value[Val, Reading[Y]],
      timeout: FiniteDuration,
      cont: Flow[Action, Val, F[Y ++ Reading[Y]], B],
    ) extends PropagateValueRes[Action, Val, F, B]

    case class ActionRequest[Action[_, _], Val[_], F[_], X, Y, B](
      input: Value[Val, X],
      action: Action[X, Y],
      cont: Flow[Action, Val, F[Y], B],
    ) extends PropagateValueRes[Action, Val, F, B]
  }

  /** Result of feeding `X`-typed value into `Work[V[X], W]`, for some type `X`. */
  sealed trait FeedValueRes[Action[_, _], Val[_], V[_], W]

  object FeedValueRes {
    case class Complete[Action[_, _], Val[_], W](
      result: Input[Val, W],
    ) extends FeedValueRes[Action, Val, [x] =>> x, W]

    case class Transformed[Action[_, _], Val[_], V[_], X, W](
      newInput: Input[Val, X],
      f: Flow[Action, Val, V[X], W],
    ) extends FeedValueRes[Action, Val, V, W]

    case class Absorbed[Action[_, _], Val[_], V[_], V0, W](
      k: Knitted[**, V, V0],
      f: Flow[Action, Val, V0, W],
    ) extends FeedValueRes[Action, Val, V, W]

    case class Shrunk[Action[_, _], Val[_], V[_], X, W](
      newValue: Input[Val, X],
      p: Projection[**, V[X], W],
    ) extends FeedValueRes[Action, Val, V, W]

    case class Read[Action[_, _], Val[_], X]()
    extends FeedValueRes[Action, Val, [x] =>> x, PortName[X] ** Reading[X]]

    case class ReadAwaitTimeout[Action[_, _], Val[_], X](
      toAwait: Value[Val, Reading[X]],
      timeout: FiniteDuration,
    ) extends FeedValueRes[Action, Val, [x] =>> x, X ++ Reading[X]]

    case class ActionRequest[Action[_, _], Val[_], X, Y](
      input: Value[Val, X],
      action: Action[X, Y],
    ) extends FeedValueRes[Action, Val, [x] =>> x, Y]
  }
}
