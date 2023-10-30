package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{Capture, Focus, Knit, Knitted, Projection, Spine, SymmetricSemigroupalCategory, UnhandledCase, Unzippable}
import libretto.lambda.examples.workflow.generic.lang.{**, ++, FlowAST, InputPortRef, Reading, given}
import libretto.lambda.util.{BiInjective, Exists, SourcePos, TypeEq}
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
    FlowAST.InjectL()

  def inr[Op[_, _], Val[_], A, B]: Flow[Op, Val, B, A ++ B] =
    FlowAST.InjectR()

  def either[Op[_, _], Val[_], A, B, C](
    f: Flow[Op, Val, A, C],
    g: Flow[Op, Val, B, C],
  ): Flow[Op, Val, A ++ B, C] =
    FlowAST.Either(f, g)

  def eitherBimap[Op[_, _], Val[_], A, B, C, D](
    f: Flow[Op, Val, A, C],
    g: Flow[Op, Val, B, D],
  ): Flow[Op, Val, A ++ B, C ++ D] =
    either(f >>> inl, g >>> inr)

  def distributeLR[Op[_, _], Val[_], A, B, C]: Flow[Op, Val, A ** (B ++ C), (A ** B) ++ (A ** C)] =
    FlowAST.DistributeLR()

  def action[Op[_, _], Val[_], A, B](f: RuntimeAction[Op, Val, A, B]): Flow[Op, Val, A, B] =
    FlowAST.DomainAction(f)

  def distLR[Op[_, _], Val[_], A, B, C](captured: Value[Val, A]): Flow[Op, Val, B ++ C, (A ** B) ++ (A ** C)] =
    action(RuntimeAction.DistLR(captured))

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
      case Split(ev) =>
        val (a1, a2) = Value.unpair(ev.substituteCo(value))
        val input = ev.substituteContra(Input.Ready(a1) ** Input.Ready(a2))
        PropagateValueRes.Transformed(input, cont)
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

            case _: FlowAST.Prj1[op, x, y] =>
              summon[VA =:= (x ** y)]
              summon[W =:= x]
              val pre1: sh.Shuffled[F[A], G[x ** y]] = pre[A].to(using ev.flip.liftCo[G])
              val p: Projection.Proper[**, G[x ** y], G[x]] = Projection.discardSnd[**, x, y].at(g)
              project(pre1, p) match
                case sh.ProjectRes.Projected(p0, pre2) =>
                  PropagateValueRes.Shrunk(Input.Ready(value), p0, fromShuffled(pre2 > post))

            case _: FlowAST.Prj2[op, x, y] =>
              summon[VA =:= (x ** y)]
              summon[W =:= y]
              val pre1: sh.Shuffled[F[A], G[x ** y]] = pre[A].to(using ev.flip.liftCo[G])
              val p: Projection.Proper[**, G[x ** y], G[y]] = Projection.discardFst[**, x, y].at(g)
              project(pre1, p) match
                case sh.ProjectRes.Projected(p0, pre2) =>
                  PropagateValueRes.Shrunk(Input.Ready(value), p0, fromShuffled(pre2 > post))

            case i: FlowAST.InjectL[op, x, y] =>
              summon[VA =:= x]
              v match
                case Focus.Id() =>
                  PropagateValueRes.Transformed(
                    Input.Ready(Value.left(ev.substituteContra(value))),
                    fromShuffled(pre[x ++ y] > post),
                  )
                case v: Focus.Proper[**, V] =>
                  RuntimeAction.captureValue[Action, Val, V, A](value, v) match
                    case Exists.Some((collector, k)) =>
                      given (V[A] =:= x) = ev.flip andThen summon[VA =:= x]
                      pre.knitBw(k.at(g)) match
                        case Exists.Some((k1, pre1)) =>
                          val i1 = action(collector).to[x] >>> i
                          PropagateValueRes.Absorbed(
                            k1,
                            fromShuffled(pre1 > toShuffled(i1).at(g) > post),
                          )

            case i: FlowAST.InjectR[op, x, y] =>
              summon[VA =:= y]
              v match
                case Focus.Id() =>
                  PropagateValueRes.Transformed(
                    Input.Ready(Value.right(ev.substituteContra(value))),
                    fromShuffled(pre[x ++ y] > post),
                  )
                case v: Focus.Proper[**, V] =>
                  RuntimeAction.captureValue[Action, Val, V, A](value, v) match
                    case Exists.Some((collector, k)) =>
                      given (V[A] =:= y) = ev.flip andThen summon[VA =:= y]
                      pre.knitBw(k.at(g)) match
                        case Exists.Some((k1, pre1)) =>
                          val i1 = action(collector).to[y] >>> i
                          PropagateValueRes.Absorbed(
                            k1,
                            fromShuffled(pre1 > toShuffled(i1).at(g) > post),
                          )

            case e: FlowAST.Either[op, x, y, w] =>
              v match
                case Focus.Id() =>
                  val axy: A =:= (x ++ y) = summon[A =:= V[A]] andThen ev.flip andThen summon[VA =:= (x ++ y)]
                  val xy: Value[Val, x ++ y] = axy.substituteCo(value)
                  Value.toEither(xy) match
                    case Left(x) =>
                      PropagateValueRes.Transformed(
                        Input.Ready(x),
                        fromShuffled(pre[x] > toShuffled(e.f).at(g) > post),
                      )
                    case Right(y) =>
                      PropagateValueRes.Transformed(
                        Input.Ready(y),
                        fromShuffled(pre[y] > toShuffled(e.g).at(g) > post),
                      )
                case other =>
                  throw AssertionError(s"Impossible: would meant that `++` = `**`")

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

            case FlowAST.DoWhile(body) =>
              ev match { case TypeEq(Refl()) =>
                val f1 = body >>> FlowAST.Either(FlowAST.DoWhile(body), FlowAST.Id())
                val cont = fromShuffled(pre[A] > toShuffled(f1).at(g) > post)
                PropagateValueRes.Transformed[Action, Val, F, A, B](Input.Ready(value), cont)
              }

            case read: FlowAST.ReadAwait[op, a] =>
              v match
                case Focus.Id() =>
                  given (A =:= Reading[a]) =
                    summon[A =:= V[A]] andThen ev.flip andThen summon[VA =:= Reading[a]]
                  val ref =
                    Value.extractInPortId(value.as[Reading[a]])
                  PropagateValueRes.Transformed(
                    Input.awaiting(ref),
                    fromShuffled(pre[a] > post),
                  )
                case other =>
                  // TODO: derive contradiction
                  UnhandledCase.raise(s"propagateValue $value into $other at $v")

            case read: FlowAST.ReadAwaitTimeout[op, a] =>
              v match
                case Focus.Id() =>
                  val ev1: Reading[a] =:= A =
                    summon[Reading[a] =:= VA] andThen ev
                  val cont: Flow[Action, Val, F[a ++ Reading[a]], B] =
                    fromShuffled(pre[a ++ Reading[a]] > post)
                  val awaited: Value[Val, Reading[a]] =
                    ev1.substituteContra[Value[Val, _]](value)
                  PropagateValueRes.ReadAwaitTimeout[Action, Val, F, a, B](awaited, read.duration, cont)
                case other =>
                  // TODO: derive contradiction
                  UnhandledCase.raise(s"propagateValue $value into $other at $v")

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
                                val f1 = toShuffled(RuntimeFlows.action(RuntimeAction.partiallyApplied(r, action))).at(g)
                                val cont1 = fromShuffled(pre1 > f1 > post)
                                PropagateValueRes.Absorbed(k0, cont1)
                  }
                case d: RuntimeAction.DistLR[op, val_, x, y, z] =>
                  v match
                    case Focus.Id() =>
                      def go[X, Y, Z](
                        x: Value[Val, X],
                        yz: Value[Val, Y ++ Z],
                        post: sh.Shuffled[G[(X ** Y) ++ (X ** Z)], B],
                      ): PropagateValueRes[Action, Val, F, B] =
                        val input: Value[Val, (X ** Y) ++ (X ** Z)] =
                          Value.toEither(yz) match
                            case Left(y)  => Value.left(x ** y)
                            case Right(z) => Value.right(x ** z)
                        PropagateValueRes.Transformed(
                          Input.Ready(input),
                          fromShuffled(pre[(X ** Y) ++ (X ** Z)] > post),
                        )

                      val yz: Value[Val, y ++ z] = ev.flip.substituteCo[Value[Val, _]](value)
                      go[x, y, z](d.x, yz, post)

                    case other =>
                      throw AssertionError(s"Impossible, would mean that `++` = `**`")

                case RuntimeAction.ValueCollector(f) =>
                  v match
                    case Focus.Id() =>
                      PropagateValueRes.Transformed(
                        Input.Ready(f.complete(ev.substituteContra(value)).fold),
                        fromShuffled(pre[W] > post),
                      )
                    case v: Focus.Proper[**, V] =>
                      given (V[A] =:= VA) = ev.flip
                      f.absorb[V, A](value, v) match
                        case Capture.Absorbed.Impl(k, f1) =>
                          pre.knitBw(k.at(g)) match
                            case Exists.Some((k1, pre1)) =>
                              val f2 = toShuffled(RuntimeFlows.action(RuntimeAction.ValueCollector(f1))).at(g)
                              PropagateValueRes.Absorbed(k1, fromShuffled(pre1 > f2 > post))

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
            case v: Focus.Proper[pr, v] =>
              val ev = v.provePair[A]
              type P = ev.T
              type Q = ev.value.T
              given ev1: (V[A] =:= (P ** Q)) =
                ev.value.value
              val pre1: sh.Shuffled[F[A], G[(P ** Q) ** (Y ++ Z)]] =
                pre[A].to(using ev1.liftCo[[x] =>> G[x ** (Y ++ Z)]])
              val distSeparately: Flow[Action, Val, (P ** Q) ** (Y ++ Z), ((P ** Q) ** Y) ++ ((P ** Q) ** Z)] =
                assocLR >>> snd(distributeLR) >>> distributeLR >>> eitherBimap(assocRL, assocRL)
              val distSeparately1: Flow[Action, Val, (P ** Q) ** (Y ++ Z), (V[A] ** Y) ++ (V[A] ** Z)] =
                distSeparately.to(using ev1.liftContra[[x] =>> (x ** Y) ++ (x ** Z)])
              PropagateValueRes.Transformed(
                Input.Ready(value),
                fromShuffled(pre1 > toShuffled(distSeparately1).at(g) > post)
              )

        go[v, g, w](r.pre, r.v, r.f, r.g, r.post)
  }

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
    sealed trait Transported[Action[_, _], Val[_], F[_], X, G[_], B]
    extends PropagateValueRes[Action, Val, F, B]:
      def outFocus: Focus[**, G]
      def ev: G[X] =:= B
      def outputValue: Value[Val, X]
      def knit(k: Knit[**, G]): Exists[[F0] =>> (Knitted[**, F, F0], Flow[Action, Val, F0, k.Res])]

    object Transported {
      class Impl[Action[_, _], Val[_], F[_], X, G[_], B](using sh: Shuffled[Action, Val])(
        f: sh.Punched[F, G],
        override val ev: G[X] =:= B,
        override val outputValue: Value[Val, X],
      ) extends Transported[Action, Val, F, X, G, B]:
        override def outFocus: Focus[**, G] =
          f.focusOut
        override def knit(k: Knit[**, G]): Exists[[F0] =>> (Knitted[**, F, F0], Flow[Action, Val, F0, k.Res])] =
          f.knitBw(k) match
            case Exists.Some((k, f)) => Exists((k, fromShuffled(f)))
    }

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
      cont: Flow[Action, Val, F[InputPortRef[Y] ** Reading[Y]], B]
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
}
