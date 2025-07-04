package libretto.scaletto.impl.futurebased

import libretto.exec.Execution
import libretto.exec.Executor.CancellationReason
import libretto.lambda.EnumModule
import libretto.lambda.Items1Named.Member
import libretto.lambda.util.SourcePos
import libretto.scaletto.impl.{-⚬, Blueprint, Fun, FreeScaletto, ScalaFunction, bug}
import libretto.util.{Async, Scheduler}
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{ExecutionContext, Future, Promise}
import scala.util.{Failure, Success, Try}

private class ExecutionImpl(
  resourceRegistry: ResourceRegistry,
  blockingEC: ExecutionContext,
)(using
  ec: ExecutionContext,
  scheduler: Scheduler,
) extends Execution {
  import ResourceRegistry.*

  val dsl = FreeScaletto
  import dsl.*

  override opaque type OutPort[A] = Frontier[A]
  override opaque type InPort[A] = Frontier[A] => Unit

  private val (notifyOnCancel, watchCancellation) =
    Async.promise[CancellationReason]

  def execute[A, B](prg: A -⚬ B): (InPort[A], OutPort[B]) = {
    val input = Promise[Frontier[A]]
    val in:  InPort[A]  = fa => input.success(fa)
    val out: OutPort[B] = Frontier.Deferred(input.future).extendBy(prg)(using resourceRegistry)
    (in, out)
  }

  def cancel(pos: SourcePos): Async[Unit] = {
    val openResources: Seq[AcquiredResource[?]] =
      resourceRegistry.close()

    Async
      .awaitAll(openResources.map { r => r.release.runAsync(r.resource) })
      .map(_ => notifyOnCancel(CancellationReason.User(pos)))
  }

  def watchForCancellation(): Async[CancellationReason] =
    watchCancellation

  object OutPort {
    def map[A, B](port: OutPort[A])(f: A -⚬ B): OutPort[B] =
      port.extendBy(f)(using resourceRegistry)

    def pair[A, B](a: OutPort[A], b: OutPort[B]): OutPort[A |*| B] =
      Frontier.Pair(a, b)

    def split[A, B](port: OutPort[A |*| B]): (OutPort[A], OutPort[B]) =
      port.splitPair

    def constant[A](obj: One -⚬ A): OutPort[A] =
      Frontier.One.extendBy(obj)(using resourceRegistry)

    def discardOne(port: OutPort[One]): Unit = {
      // do nothing
    }

    def awaitDone(port: OutPort[Done]): Async[Either[Throwable, Unit]] = {
      val (complete, res) = Async.promiseLinear[Either[Throwable, Unit]]
      port.toFutureDone.onComplete {
        case Success(Frontier.DoneNow) => complete(Right(()))
        case Failure(e)                => complete(Left(e))
      }
      res
    }

    def awaitPing(port: OutPort[Ping]): Async[Either[Throwable, Unit]] = {
      val (complete, res) = Async.promiseLinear[Either[Throwable, Unit]]
      port.toFuturePing.onComplete {
        case Success(Frontier.PingNow) => complete(Right(()))
        case Failure(e)                => complete(Left(e))
      }
      res
    }

    def awaitNoPing(
      port: OutPort[Ping],
      duration: FiniteDuration,
    ): Async[Either[Either[Throwable, Unit], OutPort[Ping]]] = {
      val (complete, res) = Async.promise[Either[Either[Throwable, Unit], OutPort[Ping]]]
      port.toFuturePing.onComplete {
        case Success(Frontier.PingNow) => complete(Left(Right(())))
        case Failure(e)                => complete(Left(Left(e)))
      }
      scheduler.schedule(duration, () => complete(Right(port)))
      res
    }

    def supplyNeed(port: OutPort[Need]): Unit =
      port.fulfillWith(Future.successful(()))

    def supplyPong(port: OutPort[Pong]): Unit =
      port.fulfillPongWith(Future.successful(()))

    def awaitEither[A, B](port: OutPort[A |+| B]): Async[Either[Throwable, Either[OutPort[A], OutPort[B]]]] = {
      val (complete, res) = Async.promiseLinear[Either[Throwable, Either[OutPort[A], OutPort[B]]]]
      port.futureEither.onComplete {
        case Success(res) => complete(Right(res))
        case Failure(e)   => complete(Left(e))
      }
      res
    }

    def chooseLeft[A, B](port: OutPort[A |&| B]): OutPort[A] =
      port.chooseL

    def chooseRight[A, B](port: OutPort[A |&| B]): OutPort[B] =
      port.chooseR

    def functionInputOutput[I, O](port: OutPort[I =⚬ O]): (InPort[I], OutPort[O]) = {
      val (in, out) = port.splitPair
      val in2: InPort[I] = i => in.fulfill(i)
      (in2, out)
    }

    def awaitVal[A](port: OutPort[Val[A]]): Async[Either[Throwable, A]] = {
      val (complete, res) = Async.promiseLinear[Either[Throwable, A]]
      port.toFutureValue.onComplete {
        case Success(a) => complete(Right(a))
        case Failure(e) => complete(Left(e))
      }
      res
    }
  }

  object InPort {
    def contramap[A, B](port: InPort[B])(f: A -⚬ B): InPort[A] =
      a => port(a.extendBy(f)(using resourceRegistry))

    def pair[A, B](fa: InPort[A], fb: InPort[B]): InPort[A |*| B] =
      { ab =>
        val (a, b) = ab.splitPair
        fa(a)
        fb(b)
      }

    def split[A, B](port: InPort[A |*| B]): (InPort[A], InPort[B]) = {
      val (fna, fa) = Frontier.promise[A]
      val (fnb, fb) = Frontier.promise[B]
      port(Frontier.Pair(fa, fb))
      (
        fa => fna.fulfill(fa),
        fb => fnb.fulfill(fb)
      )
    }

    def constant[A](f: A -⚬ One): InPort[A] =
      fa => OutPort.discardOne(OutPort.map(fa)(f))

    def discardOne(port: InPort[One]): Unit =
      port(Frontier.One)

    def supplyDone(port: InPort[Done]): Unit =
      port(Frontier.DoneNow)

    def supplyPing(port: InPort[Ping]): Unit =
      port(Frontier.PingNow)

    def supplyLeft[A, B](port: InPort[A |+| B]): InPort[A] = {
      val (fna, fa) = Frontier.promise[A]
      port(Frontier.InjectL(fa))
      fa => fna.fulfill(fa)
    }

    def supplyRight[A, B](port: InPort[A |+| B]): InPort[B] = {
      val (fnb, fb) = Frontier.promise[B]
      port(Frontier.InjectR(fb))
      fb => fnb.fulfill(fb)
    }

    def supplyChoice[A, B](port: InPort[A |&| B]): Async[Either[Throwable, Either[InPort[A], InPort[B]]]] = {
      val (complete, res) = Async.promiseLinear[Either[Throwable, Either[InPort[A], InPort[B]]]]

      port(Frontier.Choice(
        { () =>
          val (fna, fa) = Frontier.promise[A]
          complete(Right(Left(fa => fna.fulfill(fa))))
          fa
        },
        { () =>
          val (fnb, fb) = Frontier.promise[B]
          complete(Right(Right(fb => fnb.fulfill(fb))))
          fb
        },
        e => complete(Left(e))
      ))

      res
    }

    def functionInputOutput[I, O](port: InPort[I =⚬ O]): (OutPort[I], InPort[O]) = {
      val (ni, i) = Frontier.promise[I]
      val (no, o) = Frontier.promise[O]
      port(Frontier.Pair(ni, o))
      (i, o => no.fulfill(o))
    }

    def supplyVal[A](port: InPort[Val[A]], value: A): Unit =
      port(Frontier.Value(value))
  }

  extension [A, B](f: ScalaFunction[A, B]) {
    def runFuture: A => Future[B] =
      f match {
        case ScalaFunction.Direct(f)       => a => Future.successful(f(a))
        case ScalaFunction.Blocking(f)     => a => Future { f(a) } (blockingEC)
        case ScalaFunction.Asynchronous(f) => a => Async.toFuture(f(a))
        case ScalaFunction.Step(f)         => a => { val (g, x) = f(a); g.runFuture(x) }
      }

    def runAsync: A => Async[B] =
      f match {
        case ScalaFunction.Direct(f)       => a => Async.now(f(a))
        case ScalaFunction.Blocking(f)     => a => Async.executeOn(blockingEC) { f(a) }
        case ScalaFunction.Asynchronous(f) => f
        case ScalaFunction.Step(f)         => a => { val (g, x) = f(a); g.runAsync(x) }
      }
  }

  private def newResource[R](r: R, release: Option[ScalaFun[R, Unit]]): Frontier[Res[R]] =
    release match {
      case None =>
        Frontier.MVal(r)
      case Some(release) =>
        resourceRegistry.registerResource(r, release) match {
          case RegisterResult.Registered(resId) =>
            Frontier.Resource(resId, r)
          case RegisterResult.RegistryClosed =>
            release
              .runFuture(r)
              .map(_ => Frontier.failure("acquired resource immediately released because shutting down"))
              .asDeferredFrontier
        }
    }

  private def unregisterResource[R](r: Frontier.ResFrontier[R]): Boolean =
    r match {
      case Frontier.MVal(r) =>
        true
      case Frontier.Resource(id, r) =>
        resourceRegistry.unregisterResource(id) match {
          case UnregisterResult.Unregistered(_) =>
            true
          case UnregisterResult.NotFound =>
            bug(s"Previously registered resource $id not found in resource registry")
          case UnregisterResult.RegistryClosed =>
            false
        }
    }

  private sealed trait Frontier[A] {
    import Frontier.*

    def extendBy[B](f: A -⚬ B)(using
      resourceRegistry: ResourceRegistry,
      ec: ExecutionContext,
      scheduler: Scheduler,
    ): Frontier[B] =
      extendBy(f, 0)

    private def extendBy[B](f: A -⚬ B, depth: Int)(using
      resourceRegistry: ResourceRegistry,
      ec: ExecutionContext,
      scheduler: Scheduler,
    ): Frontier[B] = {
      extension [X](fx: Frontier[X]) {
        def extend[Y](f: X -⚬ Y): Frontier[Y] =
          if (depth < 100)
            fx.extendBy(f, depth + 1)
          else
            Deferred(Future.successful(fx).map(_.extendBy(f, 0)))
      }

      f match {
        case r: -⚬.SelfRef[A, B] =>
          // TODO: (?) Interpret a Blueprint instead, to make this case unrepresentable?
          bug(s"Trying to execute a program with recursive self-references.")

        case -⚬.FunRef(_, f) =>
          // TODO: should be guarded, i.e. expanded only when needed
          this.extend(-⚬.fromBlueprint(f))

        case -⚬.ConstSub(f) =>
          Frontier.ConstSub(f)

        case -⚬.Regular(f) => f match

        case Fun.Id() =>
          this

        case Fun.AndThen(f, g) =>
          this.extend(f).extend(g)

        case op: Fun.Par[-⚬, a1, a2, b1, b2] =>
          val (a1, a2) = (this: Frontier[a1 |*| a2]).splitPair
          Pair(
            a1.extend(op.f1),
            a2.extend(op.f2),
          )

        case Fun.IntroFst() =>
          Pair(One, this)

        case Fun.IntroSnd() =>
          Pair(this, One)

        case _: Fun.ElimFst[x] =>
          (this: Frontier[One |*| x])
            .splitPair
            ._2

        case _: Fun.ElimSnd[x] =>
          (this: Frontier[x |*| One])
            .splitPair
            ._1

        case _: Fun.AssocLR[x, y, z] =>
          // ((x |*| y) |*| z) -⚬ (x |*| (y |*| z))
          val (xy, z) = (this: Frontier[(x |*| y) |*| z]).splitPair
          val (x, y)  = xy.splitPair
          Pair(x, Pair(y, z))

        case _: Fun.AssocRL[x, y, z] =>
          // (x |*| (y |*| z)) -⚬ ((x |*| y) |*| z)
          val (x, yz) = (this: Frontier[x |*| (y |*| z)]).splitPair
          val (y, z) = yz.splitPair
          Pair(Pair(x, y), z)

        case _: Fun.Swap[x, y] =>
          val (x, y) = (this: Frontier[x |*| y]).splitPair
          Pair(y, x)

        case _: Fun.InjectL[x, y] =>
          InjectL[x, y](this)

        case _: Fun.InjectR[x, y] =>
          InjectR[x, y](this)

        case op: Fun.EitherF[-⚬, a1, a2, b] =>
          val Fun.EitherF(f, g) = op
          def go(a12: Frontier[a1 |+| a2]): Frontier[B] =
            a12 match {
              case InjectL(a1) =>
                a1.extend(f)
              case InjectR(a2) =>
                a2.extend(g)
              case Deferred(fa12) =>
                Deferred(fa12.map(go))
            }
          go(this: Frontier[a1 |+| a2])

        case Fun.Absurd() =>
          this.absurd

        case Fun.OneOfInject(i) =>
          OneOfInject(this, i)

        case op: Fun.OneOfHandle[-⚬, cases, b] =>
          summon[A =:= OneOf[cases]]
          summon[B =:= b]

          def go(in: Frontier[OneOf[cases]]): Frontier[B] =
            in match {
              case OneOfInject(a, i) =>
                a.extend(op.handlers.get(i))
              case Deferred(fa) =>
                Deferred(fa.map(go))
            }

          go(this)

        case _: Fun.ChooseL[a1, a2] =>
          Frontier.chooseL[a1, a2](this)

        case _: Fun.ChooseR[a1, a2] =>
          Frontier.chooseR[a1, a2](this)

        case op: Fun.Choice[-⚬, x1, x2, y] =>
          val Fun.Choice(f, g) = op
          Choice(
            () => this.extendBy(f),
            () => this.extendBy(g),
            onError = this.crash(_),
          )

        case Fun.PingF() =>
          // Ignore `this`. It ends in `One`, so it does not need to be taken care of.
          PingNow

        case Fun.PongF() =>
          this.fulfillPongWith(Future.successful(()))
          One

        case f @ Fun.DelayIndefinitely() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case f @ Fun.RegressInfinitely() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case Fun.Fork() =>
          Pair(this, this)

        case Fun.ForkPing() =>
          Pair(this, this)

        case Fun.NotifyDoneL() =>
          // Done -⚬ (Ping |*| Done)
          val d: Frontier[Done] = this
          val wd: Frontier[Ping] = d match {
            case DoneNow => PingNow
            case d => d.toFutureDone.map(_ => PingNow).asDeferredFrontier
          }
          Pair(wd, d)

        case Fun.Join() =>
          def go(f1: Frontier[Done], f2: Frontier[Done]): Frontier[Done] =
            (f1, f2) match {
              case (DoneNow, d2) => d2
              case (d1, DoneNow) => d1
              case (Deferred(f1), Deferred(f2)) =>
                Deferred((f1 zipWith f2)(go))
            }
          val (d1, d2) = (this: Frontier[Done |*| Done]).splitPair
          go(d1, d2)

        case Fun.JoinPing() =>
          // (Ping |*| Ping) -⚬ Ping

          def go(f1: Frontier[Ping], f2: Frontier[Ping]): Frontier[Ping] =
            (f1, f2) match {
              case (PingNow, d2) => d2
              case (d1, PingNow) => d1
              case (Deferred(f1), Deferred(f2)) =>
                Deferred((f1 zipWith f2)(go))
            }

          val (d1, d2) = (this: Frontier[Ping |*| Ping]).splitPair
          go(d1, d2)

        case Fun.ForkNeed() =>
          val p = Promise[Any]()
          val (n1, n2) = (this: Frontier[Need |*| Need]).splitPair
          n1 fulfillWith p.future
          n2 fulfillWith p.future
          NeedAsync(p)

        case Fun.ForkPong() =>
          val p = Promise[Any]()
          val (p1, p2) = (this: Frontier[Pong |*| Pong]).splitPair
          p1 fulfillPongWith p.future
          p2 fulfillPongWith p.future
          PongAsync(p)

        case Fun.NotifyNeedL() =>
          // (Pong |*| Need) -⚬ Need
          val (wn, n) = (this: Frontier[Pong |*| Need]).splitPair
          val p = Promise[Any]()
          wn fulfillPongWith p.future
          n fulfillWith p.future
          NeedAsync(p)

        case Fun.JoinNeed() =>
          val p1 = Promise[Any]()
          val p2 = Promise[Any]()
          this.fulfillWith(p1.future zip p2.future)
          Pair(NeedAsync(p1), NeedAsync(p2))

        case Fun.JoinPong() =>
          val p1 = Promise[Any]()
          val p2 = Promise[Any]()
          this.fulfillPongWith(p1.future zip p2.future)
          Pair(PongAsync(p1), PongAsync(p2))

        case Fun.StrengthenPing() =>
          // Ping -⚬ Done
          this match {
            case PingNow => DoneNow
            case other => other.toFuturePing.map { case PingNow => DoneNow }.asDeferredFrontier
          }

        case Fun.StrengthenPong() =>
          // Need -⚬ Pong
          val p = Promise[Any]()
          this.fulfillWith(p.future)
          PongAsync(p)

        case _: Fun.NotifyEither[x, y] =>
          // (x |+| y) -⚬ (Ping |*| (x |+| y))

          def go(xy: Frontier[x |+| y]): Frontier[Ping |*| (x |+| y)] =
            xy match {
              case l @ InjectL(_) => Pair(PingNow, l)
              case r @ InjectR(_) => Pair(PingNow, r)
              case other =>
                val decided = other.switch(_ => PingNow)
                Pair(decided, other)
            }

          go(this: Frontier[x |+| y])

        case _: Fun.NotifyChoice[x, y] =>
          // (Pong |*| (x |&| y)) -⚬ (x |&| y)
          (this: Frontier[Pong |*| (x |&| y)]).splitPair match {
            case (n, c) =>
              Choice(
                () => {
                  n fulfillPongWith Future.successful(())
                  Frontier.chooseL(c)
                },
                () => {
                  n fulfillPongWith Future.successful(())
                  Frontier.chooseR(c)
                },
                onError = { e =>
                  n fulfillPongWith Future.failed(e)
                  c.asChoice.onError(e)
                },
              )
          }

        case _: Fun.InjectLOnPing[x, y] =>
          // (Ping |*| x) -⚬ (x |+| y)

          val (p, x) = (this: Frontier[Ping |*| x]).splitPair
          p match {
            case PingNow =>
              InjectL[x, y](x)
            case p =>
              p
                .toFuturePing
                .map { case PingNow => InjectL[x, y](x) }
                .asDeferredFrontier
          }

        case _: Fun.ChooseLOnPong[x, y] =>
          // (x |&| y) -⚬ (Pong |*| x)
          val Choice(fx, fy, onError) = (this: Frontier[x |&| y]).asChoice
          val pp = Promise[Any]()
          val px = Promise[Frontier[x]]()
          pp.future.onComplete {
            case Failure(e) =>
              onError(e)
              px.failure(e)
            case Success(_) =>
              px.success(fx())
          }
          Pair(PongAsync(pp), Deferred(px.future))

        case _: Fun.DistributeL[x, y, z] =>
          // (x |*| (y |+| z)) -⚬ ((x |*| y) |+| (x |*| z))

          (this: Frontier[x |*| (y |+| z)]).splitPair match {
            case (x, InjectL(y)) => InjectL[x |*| y, x |*| z](Pair(x, y))
            case (x, InjectR(z)) => InjectR[x |*| y, x |*| z](Pair(x, z))
            case (x, fyz) =>
              fyz
                .switch[(x |*| y) |+| (x |*| z)] {
                  case Left(y) => InjectL(Pair(x, y))
                  case Right(z) => InjectR(Pair(x, z))
                }
          }

        case op: Fun.DistributeNAryLR[d, cases, dCases] =>
          summon[A =:= (d |*| OneOf[cases])]
          summon[B =:= OneOf[dCases]]

          val (d, cs) = (this: Frontier[d |*| OneOf[cases]]).splitPair

          def go(cs: Frontier[OneOf[cases]]): Frontier[OneOf[dCases]] =
            cs match
              case OneOfInject(a, i) =>
                OneOfInject(Pair(d, a), op.dist.distributeOver(i))
              case Deferred(cs) =>
                Deferred(cs.map(go))

          go(cs)

        case op: Fun.DistributeNAryRL[d, cases, dCases] =>
          summon[A =:= (OneOf[cases] |*| d)]
          summon[B =:= OneOf[dCases]]

          val (cs, d) = (this: Frontier[OneOf[cases] |*| d]).splitPair

          def go(cs: Frontier[OneOf[cases]]):Frontier[OneOf[dCases]] =
            cs match
              case OneOfInject(a, i) =>
                OneOfInject(Pair(a, d), op.dist.distributeOver(i))
              case Deferred(cs) =>
                Deferred(cs.map(go))

          go(cs)

        case _: Fun.CoDistributeL[x, y, z] =>
          // ((x |*| y) |&| (x |*| z)) -⚬ (x |*| (y |&| z))
          (this: Frontier[(x |*| y) |&| (x |*| z)]).asChoice match {
            case Choice(f, g, onError) =>
              val px = Promise[Frontier[x]]()
              val chooseL: () => Frontier[y] = { () =>
                val (x, y) = Frontier.splitPair(f())
                px.success(x)
                y
              }
              val chooseR: () => Frontier[z] = { () =>
                val (x, z) = Frontier.splitPair(g())
                px.success(x)
                z
              }
              val onError1: Throwable => Unit = { e =>
                onError(e)
                px.failure(e)
              }
              Pair(Deferred(px.future), Choice(chooseL, chooseR, onError1))
          }

        case Fun.RInvertSignal() =>
          // (Done |*| Need) -⚬ One
          val (d, n) = (this: Frontier[Done |*| Need]).splitPair
          n fulfillWith d.toFutureDone
          One

        case Fun.RInvertPingPong() =>
          // (Ping |*| Pong) -⚬ One
          val (d, n) = (this: Frontier[Ping |*| Pong]).splitPair
          n fulfillPongWith d.toFuturePing
          One

        case Fun.LInvertSignal() =>
          // One -⚬ (Need |*| Done)
          this.awaitIfDeferred
          val p = Promise[Any]()
          Pair(
            NeedAsync(p),
            Deferred(p.future.map(_ => DoneNow)),
          )

        case Fun.LInvertPongPing() =>
          // One -⚬ (Pong |*| Ping)
          this.awaitIfDeferred
          val p = Promise[Any]()
          Pair(
            PongAsync(p),
            Deferred(p.future.map(_ => PingNow)),
          )

        case Fun.RecFun(f) =>
          Pair(RecOccurrence(f), this).extend(f)

        case _: Fun.InvokeSub[x, b] =>
          val (rc, x) = (this: Frontier[Sub[x, B] |*| x]).splitPair

          def go[X, Y](rc: Frontier[Sub[X, Y]], x: Frontier[X]): Frontier[Y] =
            rc match
              case ConstSub(f)                    => x.extend(-⚬.fromBlueprint(f))
              case r @ RecOccurrence(f)           => Pair(r, x).extend(f)
              case ParameterizedSub(p, _, _, prc) => go(prc, Pair(p, x))
              case Deferred(f)                    => Deferred(f.map(go(_, x)))

          go(rc, x)

        case _: Fun.IgnoreSub[x, y] =>
          def go[X, Y](rc: Frontier[Sub[X, Y]]): Frontier[One] =
            rc match
              case RecOccurrence(_) | ConstSub(_) =>
                Frontier.One
              case ParameterizedSub(p, disP, dupP, prc) =>
                p.extend(disP)
                go(prc)
              case Deferred(f) =>
                Deferred(f.map(go))

          go(this: Frontier[Sub[x, y]])

        case _: Fun.DupSub[x, y] =>
          summon[A =:= Sub[x, y]]
          summon[B =:= (Sub[x, y] |*| Sub[x, y])]

          def go[X, Y](rc: Frontier[Sub[X, Y]]): Frontier[Sub[X, Y] |*| Sub[X, Y]] =
            rc match
              case c @ ConstSub(_) =>
                Pair(c, c)
              case r @ RecOccurrence(_) =>
                Pair(r, r)
              case ParameterizedSub(p, disP, dupP, prc) =>
                val (p1, p2) = p.extend(dupP).splitPair
                val (rc1, rc2) = go(prc).splitPair
                Pair(
                  ParameterizedSub(p1, disP, dupP, rc1),
                  ParameterizedSub(p2, disP, dupP, rc2),
                )
              case Deferred(f) =>
                Deferred(f.map(go))

          go[x, y](this)

        case f: Fun.CaptureIntoSub[-⚬, x, a, b] =>
          summon[A =:= (Sub[x |*| a, b] |*| x)]
          summon[B =:= Sub[a, b]]

          val (rc, x) = (this: Frontier[Sub[x |*| a, b] |*| x]).splitPair
          ParameterizedSub[x, a, b](
            x,
            f.discardCapture,
            f.splitCapture,
            rc,
          )

        case _: Fun.Pack[f] =>
          Pack[f](this: Frontier[f[Rec[f]]])

        case _: Fun.Unpack[f] =>
          def go(f: Frontier[Rec[f]]): Frontier[f[Rec[f]]] =
            f match {
              case Pack(f) => f
              case Deferred(f) => Deferred(f.map(go))
            }
          go(this: Frontier[Rec[f]])

        case Fun.RacePair() =>
          def go(x: Frontier[Ping], y: Frontier[Ping]): Frontier[One |+| One] =
            (x, y) match {
              case (PingNow, y) => InjectL(One) // y is ignored
              case (x, PingNow) => InjectR(One) // x is ignored
              case (x, y) =>
                // check the first one for completion in order to be (somewhat) left-biased
                val fx = x.toFuturePing
                fx.value match {
                  case Some(res) =>
                    // x completed, y is ignored
                    res match {
                      case Success(PingNow) => InjectL(One)
                      case Failure(e)           => Deferred(Future.failed(e))
                    }
                  case None =>
                    val fy = y.toFuturePing
                    val p = Promise[Frontier[One |+| One]]
                    fx.onComplete(r => p.tryComplete(r.map(_ => InjectL(One))))
                    fy.onComplete(r => p.tryComplete(r.map(_ => InjectR(One))))
                    Deferred(p.future)
                }
            }

          val (x, y) = (this: Frontier[Ping |*| Ping]).splitPair
          go(x, y)

        case Fun.SelectPair() =>
          // XXX: not left-biased. What does it even mean, precisely, for a racing operator to be biased?
          val Choice(f, g, onError) = (this: Frontier[One |&| One]).asChoice
          val p1 = Promise[Any]()
          val p2 = Promise[Any]()
          val p = Promise[() => Frontier[One]]
          p1.future.onComplete(r => p.tryComplete(r.map(_ => f)))
          p2.future.onComplete(r => p.tryComplete(r.map(_ => g)))
          p.future.onComplete {
            case Success(one) => one(): Frontier[One] // can be ignored
            case Failure(e) => onError(e)
          }
          Pair(PongAsync(p1), PongAsync(p2))

        case op: Fun.CrashWhenDone[x, b] =>
          // (Done |*| x) -⚬ B

          val (d, x) = (this: Frontier[Done |*| x]).splitPair
          d
            .toFutureDone
            .transformWith[Frontier[B]] { res =>
              val e = res match {
                case Success(DoneNow) => Crash(op.msg)
                case Failure(e) => e
              }
              x.crash(e)
              Future.failed(e)
            }
            .asDeferredFrontier

        case Fun.Delay() =>
          // Val[FiniteDuration] -⚬ Done
          (this: Frontier[Val[FiniteDuration]])
            .toFutureValue
            .flatMap { d =>
              val p = Promise[DoneNow.type]()
              scheduler.schedule(d, () => p.success(DoneNow))
              p.future
            }
            .asDeferredFrontier

        case _: Fun.LiftEither[a1, a2] =>
          def go[X, Y](xy: Either[X, Y]): Frontier[Val[X] |+| Val[Y]] =
            xy match {
              case Left(x)  => InjectL(Value(x))
              case Right(y) => InjectR(Value(y))
            }
          (this: Frontier[Val[Either[a1, a2]]]) match {
            case Value(e) => go(e)
            case a        => a.toFutureValue.map(go).asDeferredFrontier
          }

        case _: Fun.LiftPair[a1, a2] =>
          // Val[(a1, a2)] -⚬ (Val[a1] |*| Val[a2])
          (this: Frontier[Val[(a1, a2)]]) match {
            case Value((a1, a2)) =>
              Pair(Value(a1), Value(a2))
            case a =>
              val fa12 = a.toFutureValue
              Pair(
                fa12.map(_._1).toValFrontier,
                fa12.map(_._2).toValFrontier,
              )
          }

        case _: Fun.UnliftPair[x, y] =>
          // (Val[x] |*| Val[y]) -⚬ Val[(x, y)]
          val (x, y) = Frontier.splitPair(this: Frontier[Val[x] |*| Val[y]])
          (x.toFutureValue zip y.toFutureValue).toValFrontier

        case op: Fun.MapVal[x, y] =>
          (this: Frontier[Val[x]])
            .toFutureValue
            .flatMap(op.f.runFuture)
            .toValFrontier

        case Fun.ConstVal(a) =>
          this
            .toFutureDone
            .map(_ => a)
            .toValFrontier

        case op: Fun.ConstNeg[x] =>
          val pu = Promise[Any]()
          (this: Frontier[Neg[x]])
            .completeWith(pu.future.map(_ => op.a))
          NeedAsync(pu)

        case _: Fun.Neglect[x] =>
          (this: Frontier[Val[x]])
            .toFutureValue
            .map(_ => DoneNow)
            .asDeferredFrontier

        case _: Fun.NotifyVal[x] =>
          // Val[x] -⚬ (Ping |*| Val[x])
          val (fd: Frontier[Ping], fx: Frontier[Val[x]]) =
            (this: Frontier[Val[x]]) match {
              case x @ Value(_) =>
                (PingNow, x)
              case fx =>
                (fx.toFutureValue.map(_ => PingNow).asDeferredFrontier, fx)
            }
          Pair(fd, fx)

        case _: Fun.NotifyNeg[x] =>
          // (Pong |*| Neg[x]) -⚬ Neg[x]
          val (n, x) = (this: Frontier[Pong |*| Neg[x]]).splitPair
          n fulfillPongWith x.future
          x

        case Fun.DebugPrint(msg) =>
          // Ping -⚬ One
          this.toFuturePing.onComplete {
            case Success(PingNow) => println(msg)
            case Failure(e)       => e.printStackTrace(System.err)
          }
          One

        case f @ Fun.JoinRTermini() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case f @ Fun.JoinLTermini() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case f @ Fun.RInvertTerminus() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case f @ Fun.LInvertTerminus() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case op: Fun.Acquire[x, r, y] =>
          // Val[x] -⚬ (Res[r] |*| Val[y])

          val acquire: ScalaFun[x, (r, y)]       = op.acquire
          val release: Option[ScalaFun[r, Unit]] = op.release

          def go(x: x): Frontier[Res[r] |*| Val[y]] = {
            acquire
              .runFuture(x)
              .map { case (r, y) => Pair(newResource(r, release), Value(y)) }
              .asDeferredFrontier
          }

          (this: Frontier[Val[x]]) match {
            case Value(x) => go(x)
            case x => x.toFutureValue.map(go).asDeferredFrontier
          }

        case op: Fun.TryAcquire[x, r, y, e] =>
          // Val[x] -⚬ (Val[e] |+| (Res[r] |*| Val[y]))

          val acquire: ScalaFun[x, Either[e, (r, y)]] = op.acquire
          val release: Option[ScalaFun[r, Unit]]      = op.release

          def go(x: x): Frontier[Val[e] |+| (Res[r] |*| Val[y])] = {
            def go1(res: Either[e, (r, y)]): Frontier[Val[e] |+| (Res[r] |*| Val[y])] =
              res match {
                case Left(e) =>
                  InjectL(Value(e))
                case Right((r, y)) =>
                  InjectR(Pair(newResource(r, release), Value(y)))
              }

            acquire.runAsync(x) match {
              case Async.Now(value) => go1(value)
              case other => Async.toFuture(other).map(go1).asDeferredFrontier
            }
          }

          (this: Frontier[Val[x]]) match {
            case Value(x) => go(x)
            case x => x.toFutureValue.map(go).asDeferredFrontier
          }

        case op: Fun.Effect[r, x, y] =>
          // (Res[r] |*| Val[x]) -⚬ (Res[r] |*| Val[y])

          val f: ScalaFun[(r, x), y] =
            op.f

          def go(fr: ResFrontier[r], x: x): Frontier[Res[r] |*| Val[y]] =
            fr match {
              case fr @ MVal(r)         => f.runAsync(r, x).map(y => Pair(fr, Value(y))).asAsyncFrontier
              case fr @ Resource(id, r) => f.runAsync(r, x).map(y => Pair(fr, Value(y))).asAsyncFrontier
            }

          (this: Frontier[Res[r] |*| Val[x]]).splitPair match {
            case (r: ResFrontier[r], Value(x)) => go(r, x)
            case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
          }

        case op: Fun.EffectWr[r, x] =>
          // (Res[r] |*| Val[x]) -⚬ Res[r]

          val f: ScalaFun[(r, x), Unit] =
            op.f

          def go(fr: ResFrontier[r], x: x): Frontier[Res[r]] =
            fr match {
              case fr @ MVal(r)         => f.runAsync(r, x).map(_ => fr).asAsyncFrontier
              case fr @ Resource(id, r) => f.runAsync(r, x).map(_ => fr).asAsyncFrontier
            }

          (this: Frontier[Res[r] |*| Val[x]]).splitPair match {
            case (r: ResFrontier[r], Value(x)) => go(r, x)
            case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
          }

        case op: Fun.TryTransformResource[r, x, s, y, e] =>
          // (Res[r] |*| Val[x]) -⚬ (Val[e] |+| (Res[s] |*| Val[y]))

          val f: ScalaFunction[(r, x), Either[e, (s, y)]] = op.f
          val release: Option[ScalaFunction[s, Unit]]     = op.release

          def go(r: ResFrontier[r], x: x): Frontier[Val[e] |+| (Res[s] |*| Val[y])] = {
            def go1(r: r, x: x): Frontier[Val[e] |+| (Res[s] |*| Val[y])] =
              f.runAsync(r, x)
                .map[Frontier[Val[e] |+| (Res[s] |*| Val[y])]] {
                  case Left(e) =>
                    InjectL(Value(e))
                  case Right((s, y)) =>
                    InjectR(Pair(newResource(s, release), Value(y)))
                }
                .asAsyncFrontier

            if (unregisterResource(r))
              go1(r.resource, x)
            else
              Frontier.failure("Not transforming resource because shutting down")
          }

          (this: Frontier[Res[r] |*| Val[x]]).splitPair match {
            case (r: ResFrontier[r], Value(x)) => go(r, x)
            case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
          }

        case op: Fun.TryEffectAcquire[r, x, s, y, e] =>
          // (Res[r] |*| Val[x]) -⚬ (Res[r] |*| (Val[e] |+| (Res[s] |*| Val[y])))
          val f: ScalaFunction[(r, x), Either[e, (s, y)]] = op.f
          val releaseS: Option[ScalaFunction[s, Unit]]     = op.release

          def go(rf: ResFrontier[r], x: x): Frontier[Res[r] |*| (Val[e] |+| (Res[s] |*| Val[y]))] = {
            f.runAsync(rf.resource, x)
              .map {
                case Left(e) =>
                  Pair(rf, InjectL(Value(e)))
                case Right((s, y)) =>
                  Pair(rf, InjectR(Pair(newResource(s, releaseS), Value(y))))
              }
              .asAsyncFrontier
          }

          (this: Frontier[Res[r] |*| Val[x]]).splitPair match {
            case (r: ResFrontier[r], Value(x)) => go(r, x)
            case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
          }

        case op: Fun.TrySplitResource[r, x, s, t, y, e] =>
          // (Res[r] |*| Val[x]) -⚬ (Val[e] |+| ((Res[s] |*| Res[t]) |*| Val[y]))

          val f: ScalaFun[(r, x), Either[e, (s, t, y)]] = op.f
          val releaseS: Option[ScalaFun[s, Unit]]       = op.release1
          val releaseT: Option[ScalaFun[t, Unit]]       = op.release2

          def go(r: ResFrontier[r], x: x): Frontier[Val[e] |+| ((Res[s] |*| Res[t]) |*| Val[y])] = {
            def go1(r: r, x: x): Frontier[Val[e] |+| ((Res[s] |*| Res[t]) |*| Val[y])] =
              f.runAsync(r, x)
                .map[Frontier[Val[e] |+| ((Res[s] |*| Res[t]) |*| Val[y])]] {
                  case Left(e) =>
                    InjectL(Value(e))
                  case Right((s, t, y)) =>
                    val fs: Frontier[Res[s]] = newResource(s, releaseS)
                    val ft: Frontier[Res[t]] = newResource(t, releaseT)
                    InjectR(Pair(Pair(fs, ft), Value(y)))
                }
                .asAsyncFrontier

            if (unregisterResource(r))
              go1(r.resource, x)
            else
              Frontier.failure("Not going to split the resource because shutting down")
          }

          (this: Frontier[Res[r] |*| Val[x]]).splitPair match {
            case (r: ResFrontier[r], Value(x)) => go(r, x)
            case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
          }

        case op: Fun.ReleaseWith[r, x, y] =>
          // (Res[r] |*| Val[x]) -⚬ Val[]

          val release: ScalaFun[(r, x), y] =
            op.f

          def go(r: ResFrontier[r], x: x): Frontier[Val[y]] =
            if (unregisterResource(r))
              release.runAsync(r.resource, x).map(Value(_)).asAsyncFrontier
            else
              Frontier.failure("Not releasing resource because shutting down. It was or will be released as part of the shutdown")

          (this: Frontier[Res[r] |*| Val[x]]).splitPair match {
            case (r: ResFrontier[r], Value(x)) => go(r, x)
            case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
          }

        case _: Fun.Release[r] =>
          // Res[R] -⚬ Done

          def go(r: ResFrontier[r]): Frontier[Done] =
            r match {
              case MVal(r) =>
                // no release needed, done
                DoneNow
              case Resource(id, r) =>
                resourceRegistry.unregisterResource(id) match {
                  case UnregisterResult.Unregistered(r) =>
                    r.release.runAsync(r.resource).map(_ => DoneNow).asAsyncFrontier
                  case UnregisterResult.NotFound =>
                    bug(s"Previously registered resource $id not found in resource registry")
                  case UnregisterResult.RegistryClosed =>
                    Frontier.failure("Not releasing resource because shutting down. It was or will be released as part of the shutdown")
                }
            }

          (this: Frontier[Res[r]]) match {
            case r: ResFrontier[r] => go(r)
            case r => r.toFutureRes.map(go).asDeferredFrontier
          }

        case _: Fun.Backvert[x] =>
          // (x |*| -[x]) -⚬ One

          val (fw, bw) = (this: Frontier[x |*| -[x]]).splitPair
          bw.fulfill(fw)
          One

        case _: Fun.Forevert[x] =>
          // One -⚬ (-[x] |*| x)

          this.awaitIfDeferred

          val pfx = Promise[Frontier[x]]()
          Pair(
            Backwards(pfx),
            Deferred(pfx.future),
          )

        case _: Fun.DistributeInversion[x, y] =>
          // -[x |*| y] -⚬ (-[x] |*| -[y])

          val px = Promise[Frontier[x]]()
          val py = Promise[Frontier[y]]()

          (this: Frontier[-[x |*| y]])
            .fulfill(Pair(px.future.asDeferredFrontier, py.future.asDeferredFrontier))

          Pair(Backwards(px), Backwards(py))

        case _: Fun.FactorOutInversion[x, y] =>
          // (-[x] |*| -[y]) -⚬ -[x |*| y]

          val (fpx, fpy) = (this: Frontier[-[x] |*| -[y]]).splitPair
          val pfxy = Promise[Frontier[x |*| y]]()
          val ffxfy = pfxy.future.map(_.splitPair)
          fpx.fulfill(ffxfy.map(_._1))
          fpy.fulfill(ffxfy.map(_._2))

          Backwards(pfxy)
      }
    }

    private def crash(e: Throwable)(using ExecutionContext): Unit = {
      this match {
        case One | DoneNow | PingNow | Value(_) | MVal(_) | Resource(_, _) =>
          // do nothing
        case NeedAsync(promise) =>
          promise.failure(e)
        case PongAsync(promise) =>
          promise.failure(e)
        case Backwards(promise) =>
          promise.failure(e)
        case Pair(a, b) =>
          a.crash(e)
          b.crash(e)
        case InjectL(a) =>
          a.crash(e)
        case InjectR(b) =>
          b.crash(e)
        case OneOfInject(a, _) =>
          a.crash(e)
        case Choice(_, _, onError) =>
          onError(e)
        case Deferred(fa) =>
          fa.map(_.crash(e))
        case Pack(f) =>
          f.crash(e)
        case RecOccurrence(_) | ConstSub(_) =>
          // has not been invoked yet, do nothing
        case ParameterizedSub(p, _, _, rc) =>
          p.crash(e)
          rc.crash(e)
      }
    }
  }

  private object Frontier {
    case object One extends Frontier[dsl.One]
    case object DoneNow extends Frontier[Done]
    case object PingNow extends Frontier[Ping]
    case class NeedAsync(promise: Promise[Any]) extends Frontier[Need]
    case class PongAsync(promise: Promise[Any]) extends Frontier[Pong]
    case class Pair[A, B](a: Frontier[A], b: Frontier[B]) extends Frontier[A |*| B]
    case class InjectL[A, B](a: Frontier[A]) extends Frontier[A |+| B]
    case class InjectR[A, B](b: Frontier[B]) extends Frontier[A |+| B]
    case class OneOfInject[Label, A, Cases](a: Frontier[A], i: Member[||, ::, Label, A, Cases]) extends Frontier[OneOf[Cases]]
    case class Choice[A, B](a: () => Frontier[A], b: () => Frontier[B], onError: Throwable => Unit) extends Frontier[A |&| B]
    case class Deferred[A](f: Future[Frontier[A]]) extends Frontier[A]
    case class Pack[F[_]](f: Frontier[F[Rec[F]]]) extends Frontier[Rec[F]]
    case class ConstSub[A, B](f: Blueprint[A, B]) extends Frontier[Sub[A, B]]
    case class RecOccurrence[A, B](f: (Sub[A, B] |*| A) -⚬ B) extends Frontier[Sub[A, B]]
    case class ParameterizedSub[P, A, B](
      p: Frontier[P],
      discardParam: P -⚬ One,
      splitParam: P -⚬ (P |*| P),
      sub: Frontier[Sub[P |*| A, B]],
    ) extends Frontier[Sub[A, B]]
    sealed trait Void extends Frontier[dsl.Void] {
      def absurd[A]: Frontier[A]
    }

    case class Value[A](a: A) extends Frontier[Val[A]]

    sealed trait ResFrontier[A] extends Frontier[Res[A]] {
      def resource: A =
        this match {
          case MVal(a) => a
          case Resource(_, a) => a
        }
    }
    case class MVal[A](value: A) extends ResFrontier[A]
    case class Resource[A](id: ResId, obj: A) extends ResFrontier[A]

    case class Backwards[A](promise: Promise[Frontier[A]]) extends Frontier[-[A]]

    def promise[A]: (Frontier[-[A]], Frontier[A]) = {
      val pa = Promise[Frontier[A]]
      (Backwards(pa), Deferred(pa.future))
    }

    def failure[A](msg: String): Frontier[A] =
      Deferred(Future.failed(new Exception(msg)))

    extension (n: Frontier[Need]) {
      infix def fulfillWith(f: Future[Any])(using ExecutionContext): Unit =
        n match {
          case NeedAsync(p) =>
            p.completeWith(f)
          case Deferred(fn) =>
            fn.onComplete {
              case Success(n) => n fulfillWith f
              case Failure(e) =>
                e.printStackTrace(System.err)
                f.onComplete {
                  case Success(_) => // do nothing
                  case Failure(ex) => ex.printStackTrace(System.err)
                }
            }
        }
    }

    extension (n: Frontier[Pong]) {
      infix def fulfillPongWith(f: Future[Any])(using ExecutionContext): Unit =
        n match {
          case PongAsync(p) =>
            p.completeWith(f)
          case Deferred(fn) =>
            fn.onComplete {
              case Success(n) => n fulfillPongWith f
              case Failure(e) =>
                e.printStackTrace(System.err)
                f.onComplete {
                  case Success(_) => // do nothing
                  case Failure(ex) => ex.printStackTrace(System.err)
                }
            }
        }
    }

    extension [A, B](f: Frontier[A |+| B]) {
      def futureEither(using ExecutionContext): Future[Either[Frontier[A], Frontier[B]]] =
        f match {
          case InjectL(a) => Future.successful(Left(a))
          case InjectR(b) => Future.successful(Right(b))
          case Deferred(fab) => fab.flatMap(_.futureEither)
        }

      def switch[C](
        g: Either[Frontier[A], Frontier[B]] => Frontier[C]
      )(using ExecutionContext): Frontier[C] =
        f match
          case InjectL(a) => g(Left(a))
          case InjectR(b) => g(Right(b))
          case Deferred(fab) => Deferred(fab.map(_.switch(g)))
    }

    extension (f: Frontier[dsl.Void]) {
      def absurd[A](using ExecutionContext): Frontier[A] =
        f match
          case Deferred(f) => Deferred(f.map(_.absurd[A]))
    }

    extension [A, B](f: Frontier[A |&| B]) {
      def chooseL(using ExecutionContext): Frontier[A] =
        f match {
          case Choice(a, b, onError) => a()
          case Deferred(f) => Deferred(f.map(_.chooseL))
        }

      def chooseR(using ExecutionContext): Frontier[B] =
        f match {
          case Choice(a, b, onError) => b()
          case Deferred(f) => Deferred(f.map(_.chooseR))
        }

      def asChoice(using ExecutionContext): Choice[A, B] =
        f match {
          case c @ Choice(_, _, _) => c
          case Deferred(f) =>
            Choice(
              () => Deferred(f.map(_.asChoice.a())),
              () => Deferred(f.map(_.asChoice.b())),
              e => f.onComplete {
                case Success(f) =>
                  f.asChoice.onError(e)
                case Failure(ex) =>
                  e.printStackTrace(System.err)
                  ex.printStackTrace(System.err)
              },
            )
        }
    }

    extension [A, B](f: Frontier[A |*| B]) {
      def splitPair(using ExecutionContext): (Frontier[A], Frontier[B]) =
        f match {
          case Pair(a, b) => (a, b)
          case Deferred(f) =>
            val fab = f.map(_.splitPair)
            (Deferred(fab.map(_._1)), Deferred(fab.map(_._2)))
        }
    }

    extension (f: Frontier[Done]) {
      def toFutureDone(using ExecutionContext): Future[DoneNow.type] =
        f match {
          case DoneNow =>
            Future.successful(DoneNow)
          case Deferred(f) =>
            f.flatMap(_.toFutureDone)
        }
    }

    extension (f: Frontier[Ping]) {
      def toFuturePing(using ExecutionContext): Future[PingNow.type] =
        f match {
          case PingNow =>
            Future.successful(PingNow)
          case Deferred(f) =>
            f.flatMap(_.toFuturePing)
        }
    }

    extension [A](f: Frontier[Val[A]]) {
      def toFutureValue(using ExecutionContext): Future[A] =
        f match {
          case Value(a) => Future.successful(a)
          case Deferred(fa) => fa.flatMap(_.toFutureValue)
        }
    }

    extension [A](f: Frontier[Res[A]]) {
      def toFutureRes(using ExecutionContext): Future[ResFrontier[A]] =
        f match {
          case f @ MVal(_) => Future.successful(f)
          case f @ Resource(_, _) => Future.successful(f)
          case Deferred(f) => f.flatMap(_.toFutureRes)
        }
    }

    extension [A](f: Frontier[Val[A]]) {
      def mapVal[B](g: A => B)(using ExecutionContext): Frontier[Val[B]] =
        f match {
          case Value(a) => Value(g(a))
          case Deferred(fa) => Deferred(fa.map(_.mapVal(g)))
        }
    }

    extension [A](f: Frontier[Neg[A]]) {
      def completeWith(fa: Future[A])(using ExecutionContext): Unit =
        f match {
          case Backwards(pfa) => pfa.success(fa.toValFrontier)
          case Deferred(f) => f.onComplete {
            case Success(f) => f.completeWith(fa)
            case Failure(e) =>
              e.printStackTrace(System.err)
              fa.onComplete {
                case Success(_) => // do nothing
                case Failure(e) => e.printStackTrace(System.err)
              }
          }
        }

      def future(using ExecutionContext): Future[A] =
        f match {
          case Backwards(pfa) => pfa.future.flatMap(_.toFutureValue)
          case Deferred(f) => f.flatMap(_.future)
        }
    }

    extension (f: Frontier[One]) {
      def awaitIfDeferred(using ExecutionContext): Unit =
        f match {
          case One => // do nothing
          case Deferred(f) =>
            f.onComplete {
              case Success(f) => f.awaitIfDeferred
              case Failure(e) => e.printStackTrace(System.err)
            }
        }
    }

    extension [A](fna: Frontier[-[A]]) {
      def fulfill(fa: Frontier[A])(using ExecutionContext): Unit =
        fna match {
          case Backwards(pfa) =>
            pfa.success(fa)
          case Deferred(ffna) =>
            ffna.onComplete {
              case Success(fna) => fna.fulfill(fa)
              case Failure(e) => e.printStackTrace(System.err)
            }
        }

      def fulfill(fa: Future[Frontier[A]])(using ExecutionContext): Unit =
        fulfill(Deferred(fa))
    }

    extension [A](fa: Future[A]) {
      def toValFrontier(using ExecutionContext): Frontier[Val[A]] =
        Deferred(fa.map(Value(_)))
    }

    extension [A](fa: Future[Frontier[A]]) {
      def asDeferredFrontier: Frontier[A] =
        Deferred(fa)
    }

    extension [A](a: Async[Frontier[A]]) {
      def asAsyncFrontier: Frontier[A] =
        a match {
          case Async.Now(fa) => fa
          case a @ Async.Later(_) => Async.toFuture(a).asDeferredFrontier
        }
    }
  }

  private case class Crash(msg: String) extends Exception(msg)
}
