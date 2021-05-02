package libretto.impl

import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.{Executor, ScheduledExecutorService, TimeUnit}
import libretto.{Async, ScalaRunner}
import scala.collection.mutable
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{ExecutionContext, Future, Promise}
import scala.util.{Failure, Success, Try}

/** Runner of [[FreeScalaDSL]] that returns a [[Future]].
  *
  * It is known to be flawed by design in that it might create long (potentially infinite) chains of [[Promise]]s.
  * This could be solved with a custom implementation of promises/futures that support unregistration of listeners.
  *
  * On top of that, expect bugs, since the implementation is full of unsafe type casts, because Scala's (including
  * Dotty's) type inference cannot cope with the kind of pattern matches found here.
  */
class FreeScalaFutureRunner(
  scheduler: ScheduledExecutorService,
  blockingExecutor: Executor,
) extends ScalaRunner[FreeScalaDSL.type, Future] {
  import ResourceRegistry._

  private implicit val ec: ExecutionContext =
    ExecutionContext.fromExecutor(scheduler)

  val dsl = FreeScalaDSL

  import dsl._

  private def bug[A](msg: String): A =
    throw new AssertionError(
      s"""$msg
         |This is a bug, please report at https://github.com/TomasMikula/libretto/issues/new?labels=bug"""
        .stripMargin
    )

  private def schedule[A](d: FiniteDuration, f: () => A): Future[A] = {
    val pa = Promise[A]()
    scheduler.schedule(() => pa.success(f()), d.length, d.unit)
    pa.future
  }

  override def runScala[A](prg: Done -⚬ Val[A]): Future[A] = {
    import Frontier._
    val resourceRegistry = new ResourceRegistry
    val fa = Frontier.DoneNow.extendBy(prg, resourceRegistry).toFutureValue

    def closeResources(openResources: Seq[AcquiredResource[_]]): Future[Any] =
      Future.traverse(openResources) { r => Async.toFuture(r.releaseAsync(r.resource)) }

    fa.transformWith {
      case Success(a) =>
        val openResources = resourceRegistry.close()
        if (openResources.isEmpty) {
          Future.successful(a)
        } else {
          System.err.println(s"Execution completed successfully, but there are ${openResources.size} unclosed resources left. Going to closie them.")
          closeResources(openResources).map { _ => a }
        }
      case Failure(e) =>
        val openResources = resourceRegistry.close()
        closeResources(openResources)
          .transformWith(_ => Future.failed[A](e)) // return the original error
    }
  }

  private sealed trait Frontier[A] {
    import Frontier._

    def extendBy[B](f: A -⚬ B, resourceRegistry: ResourceRegistry): Frontier[B] = {
      implicit class FrontierOps[X](fx: Frontier[X]) {
        def extend[Y](f: X -⚬ Y): Frontier[Y] =
        fx.extendBy(f, resourceRegistry)
      }

      f match {
        case -⚬.Id() =>
          this

        case -⚬.AndThen(f, g) =>
          this.extend(f).extend(g)

        case -⚬.Par(f, g) =>
          type A1; type A2
          val (a1, a2) = this.asInstanceOf[Frontier[A1 |*| A2]].splitPair
          Pair(
            a1.extend(f.asInstanceOf[A1 -⚬ Nothing]),
            a2.extend(g.asInstanceOf[A2 -⚬ Nothing]),
          )                                                       .asInstanceOf[Frontier[B]]

        case -⚬.IntroFst() =>
          Pair(One, this)

        case -⚬.IntroSnd() =>
          Pair(this, One)

        case -⚬.ElimFst() =>
          type X
          this
            .asInstanceOf[Frontier[One |*| X]]
            .splitPair
            ._2                                                   .asInstanceOf[Frontier[B]]

        case -⚬.ElimSnd() =>
          type X
          this
            .asInstanceOf[Frontier[X |*| One]]
            .splitPair
            ._1                                                   .asInstanceOf[Frontier[B]]

        case -⚬.AssocLR() =>
          // ((X |*| Y) |*| Z) -⚬ (X |*| (Y |*| Z))
          type X; type Y; type Z
          val (xy, z) = this.asInstanceOf[Frontier[(X |*| Y) |*| Z]].splitPair
          val (x, y) = xy.splitPair
          Pair(x, Pair(y, z))                                     .asInstanceOf[Frontier[B]]

        case -⚬.AssocRL() =>
          // (X |*| (Y |*| Z)) -⚬ ((X |*| Y) |*| Z)
          type X; type Y; type Z
          val (x, yz) = this.asInstanceOf[Frontier[X |*| (Y |*| Z)]].splitPair
          val (y, z) = yz.splitPair
          Pair(Pair(x, y), z)                                     .asInstanceOf[Frontier[B]]

        case -⚬.Swap() =>
          type X; type Y
          val (x, y) = this.asInstanceOf[Frontier[X |*| Y]].splitPair
          Pair(y, x)                                              .asInstanceOf[Frontier[B]]

        case -⚬.InjectL() =>
          InjectL(this)                                           .asInstanceOf[Frontier[B]]

        case -⚬.InjectR() =>
          InjectR(this)                                           .asInstanceOf[Frontier[B]]

        case e: -⚬.EitherF[_, _, _] =>
          val -⚬.EitherF(f, g) = e // workaround for https://github.com/lampepfl/dotty/issues/7524
          type A1; type A2
          def go(a12: Frontier[A1 |+| A2]): Frontier[B] =
            a12 match {
              case InjectL(a1) =>
                a1.extend(f.asInstanceOf[A1 -⚬ B])
              case InjectR(a2) =>
                a2.extend(g.asInstanceOf[A2 -⚬ B])
              case Deferred(fa12) =>
                Deferred(fa12.map(go))
            }
          go(this.asInstanceOf[Frontier[A1 |+| A2]])

        case -⚬.ChooseL() =>
          type A1; type A2
          Frontier.chooseL(this.asInstanceOf[Frontier[A1 |&| A2]]).asInstanceOf[Frontier[B]]

        case -⚬.ChooseR() =>
          type A1; type A2
          Frontier.chooseR(this.asInstanceOf[Frontier[A1 |&| A2]]).asInstanceOf[Frontier[B]]

        case c: -⚬.Choice[_, _, _] =>
          val -⚬.Choice(f, g) = c // workaround for https://github.com/lampepfl/dotty/issues/7524
          Choice(
            () => this.extend(f),
            () => this.extend(g),
            onError = this.crash(_),
          )

        case -⚬.PingF() =>
          // Ignore `this`. It ends in `One`, so it does not need to be taken care of.
          PingNow

        case -⚬.PongF() =>
          this.fulfillPongWith(Future.successful(()))
          One

        case f @ -⚬.DelayIndefinitely() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case f @ -⚬.RegressInfinitely() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case -⚬.Fork() =>
          Pair(this, this)

        case -⚬.NotifyDoneL() =>
          // Done -⚬ (Ping |*| Done)
          val d: Frontier[Done] = this
          val wd: Frontier[Ping] = d match {
            case DoneNow => PingNow
            case d => d.toFutureDone.map(_ => PingNow).asDeferredFrontier
          }
          Pair(wd, d)

        case -⚬.Join() =>
          def go(f1: Frontier[Done], f2: Frontier[Done]): Frontier[Done] =
            (f1, f2) match {
              case (DoneNow, d2) => d2
              case (d1, DoneNow) => d1
              case (Deferred(f1), Deferred(f2)) =>
                Deferred((f1 zipWith f2)(go))
            }
          val (d1, d2) = this.asInstanceOf[Frontier[Done |*| Done]].splitPair
          go(d1, d2)

        case -⚬.JoinPing() =>
          // (Ping |*| Ping) -⚬ Ping

          def go(f1: Frontier[Ping], f2: Frontier[Ping]): Frontier[Ping] =
            (f1, f2) match {
              case (PingNow, d2) => d2
              case (d1, PingNow) => d1
              case (Deferred(f1), Deferred(f2)) =>
                Deferred((f1 zipWith f2)(go))
            }

          val (d1, d2) = this.asInstanceOf[Frontier[Ping |*| Ping]].splitPair
          go(d1, d2)

        case -⚬.ForkNeed() =>
          val p = Promise[Any]()
          val (n1, n2) = this.asInstanceOf[Frontier[Need |*| Need]].splitPair
          n1 fulfillWith p.future
          n2 fulfillWith p.future
          NeedAsync(p)

        case -⚬.NotifyNeedL() =>
          // (Pong |*| Need) -⚬ Need
          val (wn, n) = this.asInstanceOf[Frontier[Pong |*| Need]].splitPair
          val p = Promise[Any]()
          wn fulfillPongWith p.future
          n fulfillWith p.future
          NeedAsync(p)

        case -⚬.JoinNeed() =>
          val p1 = Promise[Any]()
          val p2 = Promise[Any]()
          this.fulfillWith(p1.future zip p2.future)
          Pair(NeedAsync(p1), NeedAsync(p2))

        case -⚬.JoinPong() =>
          val p1 = Promise[Any]()
          val p2 = Promise[Any]()
          this.fulfillPongWith(p1.future zip p2.future)
          Pair(PongAsync(p1), PongAsync(p2))

        case -⚬.StrengthenPing() =>
          // Ping -⚬ Done
          this match {
            case PingNow => DoneNow
            case other => other.toFuturePing.map { case PingNow => DoneNow }.asDeferredFrontier
          }

        case -⚬.StrengthenPong() =>
          // Need -⚬ Pong
          val p = Promise[Any]()
          this.fulfillWith(p.future)
          PongAsync(p)

        case -⚬.NotifyEither() =>
          // (X |+| Y) -⚬ (Ping |*| (X |+| Y))
          type X; type Y

          def go(xy: Frontier[X |+| Y]): Frontier[Ping |*| (X |+| Y)] =
            xy match {
              case l @ InjectL(_) => Pair(PingNow, l)
              case r @ InjectR(_) => Pair(PingNow, r)
              case other =>
                val decided = other.futureEither.map(_ => PingNow).asDeferredFrontier
                Pair(decided, other)
            }

          go(this.asInstanceOf[Frontier[X |+| Y]])                .asInstanceOf[Frontier[B]]

        case -⚬.NotifyChoice() =>
          //        A             -⚬     B
          // (Pong |*| (X |&| Y)) -⚬ (X |&| Y)
          type X; type Y
          this.asInstanceOf[Frontier[Pong |*| (X |&| Y)]].splitPair match {
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
              )                                                   .asInstanceOf[Frontier[B]]
          }

        case -⚬.InjectLOnPing() =>
          // (Ping |*| X) -⚬ (X |+| Y)

          def go[X, Y](fpx: Frontier[Ping |*| X]): Frontier[X |+| Y] = {
            val (p, x) = fpx.splitPair
            p match {
              case PingNow =>
                InjectL(x)
              case p =>
                p
                  .toFuturePing
                  .map { case PingNow => InjectL(x) }
                  .asDeferredFrontier
            }
          }

          go(this.asInstanceOf)                                   .asInstanceOf[Frontier[B]]

        case -⚬.ChooseLOnPong() =>
          // (X |&| Y) -⚬ (Pong |*| X)
          type X; type Y
          val Choice(fx, fy, onError) = this.asInstanceOf[Frontier[X |&| Y]].asChoice
          val pp = Promise[Any]()
          val px = Promise[Frontier[X]]()
          pp.future.onComplete {
            case Failure(e) =>
              onError(e)
              px.failure(e)
            case Success(_) =>
              px.success(fx())
          }
          Pair(PongAsync(pp), Deferred(px.future))                .asInstanceOf[Frontier[B]]

        case -⚬.DistributeL() =>
          // (X |*| (Y |+| Z)) -⚬ ((X |*| Y) |+| (X |*| Z))

          def go[X, Y, Z](fxyz: Frontier[X |*| (Y |+| Z)]): Frontier[(X |*| Y) |+| (X |*| Z)] = {
            fxyz.splitPair match {
              case (x, InjectL(y)) => InjectL(Pair(x, y))
              case (x, InjectR(z)) => InjectR(Pair(x, z))
              case (x, fyz) =>
                fyz
                  .futureEither
                  .map[Frontier[(X |*| Y) |+| (X |*| Z)]] {
                    case Left(y) => InjectL(Pair(x, y))
                    case Right(z) => InjectR(Pair(x, z))
                  }
                  .asDeferredFrontier
            }
          }

          go(this.asInstanceOf)                                   .asInstanceOf[Frontier[B]]

        case -⚬.CoDistributeL() =>
          // ((X |*| Y) |&| (X |*| Z)) -⚬ (X |*| (Y |&| Z))
          type X; type Y; type Z
          this.asInstanceOf[Frontier[(X |*| Y) |&| (X |*| Z)]].asChoice match {
            case Choice(f, g, onError) =>
              val px = Promise[Frontier[X]]()
              val chooseL: () => Frontier[Y] = { () =>
                val (x, y) = Frontier.splitPair(f())
                px.success(x)
                y
              }
              val chooseR: () => Frontier[Z] = { () =>
                val (x, z) = Frontier.splitPair(g())
                px.success(x)
                z
              }
              val onError1: Throwable => Unit = { e =>
                onError(e)
                px.failure(e)
              }
              Pair(Deferred(px.future), Choice(chooseL, chooseR, onError1)) .asInstanceOf[Frontier[B]]
          }

        case -⚬.RInvertSignal() =>
          // (Done |*| Need) -⚬ One
          val (d, n) = this.asInstanceOf[Frontier[Done |*| Need]].splitPair
          n fulfillWith d.toFutureDone
          One

        case -⚬.RInvertPingPong() =>
          // (Ping |*| Pong) -⚬ One
          val (d, n) = this.asInstanceOf[Frontier[Ping |*| Pong]].splitPair
          n fulfillPongWith d.toFuturePing
          One

        case -⚬.LInvertSignal() =>
          // One -⚬ (Need |*| Done)
          this.awaitIfDeferred
          val p = Promise[Any]()
          Pair(
            NeedAsync(p),
            Deferred(p.future.map(_ => DoneNow)),
          )

        case -⚬.LInvertPongPing() =>
          // One -⚬ (Pong |*| Ping)
          this.awaitIfDeferred
          val p = Promise[Any]()
          Pair(
            PongAsync(p),
            Deferred(p.future.map(_ => PingNow)),
          )

        case r @ -⚬.RecF(_) =>
          this.extend(r.recursed)

        case -⚬.Pack() =>
          type F[_]
          Pack(this.asInstanceOf[Frontier[F[Rec[F]]]])            .asInstanceOf[Frontier[B]]

        case -⚬.Unpack() =>
          type F[_]
          def go(f: Frontier[Rec[F]]): Frontier[F[Rec[F]]] =
            f match {
              case Pack(f) => f
              case Deferred(f) => Deferred(f.map(go))
            }
          go(this.asInstanceOf[Frontier[Rec[F]]])                 .asInstanceOf[Frontier[B]]

        case -⚬.RacePair() =>
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

          val (x, y) = this.asInstanceOf[Frontier[Ping |*| Ping]].splitPair
          go(x, y)

        case -⚬.SelectPair() =>
          // XXX: not left-biased. What does it even mean, precisely, for a racing operator to be biased?
          val Choice(f, g, onError) = this.asInstanceOf[Frontier[One |&| One]].asChoice
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

        case -⚬.Crash(msg) =>
          // (Done |*| X) -⚬ (Done |*| Y)
          type X

          val (d, x) = this.asInstanceOf[Frontier[Done |*| X]].splitPair
          d
            .toFutureDone
            .transformWith[Frontier[B]] { res =>
              val e = res match {
                case Success(DoneNow) => Crash(msg)
                case Failure(e) => e
              }
              x.crash(e)
              Future.failed(e)
            }
            .asDeferredFrontier

        case -⚬.Delay() =>
          // Val[FiniteDuration] -⚬ Done
          this
            .asInstanceOf[Frontier[Val[FiniteDuration]]]
            .toFutureValue
            .flatMap(d => schedule(d, () => DoneNow))
            .asDeferredFrontier

        case -⚬.Promise() =>
          this.awaitIfDeferred
          type X
          val px = Promise[X]()
          Pair(Prom(px), px.future.toValFrontier)                 .asInstanceOf[Frontier[B]]

        case -⚬.Fulfill() =>
          type X
          val (x, nx) = this.asInstanceOf[Frontier[Val[X] |*| Neg[X]]].splitPair
          nx.completeWith(x.toFutureValue)
          One

        case -⚬.LiftEither() =>
          def go[X, Y](xy: Either[X, Y]): Frontier[Val[X] |+| Val[Y]] =
            xy match {
              case Left(x)  => InjectL(Value(x))
              case Right(y) => InjectR(Value(y))
            }
          type A1; type A2
          this.asInstanceOf[Frontier[Val[Either[A1, A2]]]] match {
            case Value(e) => go(e)                                .asInstanceOf[Frontier[B]]
            case a => a.toFutureValue.map(go).asDeferredFrontier  .asInstanceOf[Frontier[B]]
          }

        case -⚬.LiftPair() =>
          type A1; type A2 // such that A = Val[(A1, A2)]
          this.asInstanceOf[Frontier[Val[(A1, A2)]]] match {
            case Value((a1, a2)) =>
              Pair(Value(a1), Value(a2))                          .asInstanceOf[Frontier[B]]
            case a =>
              val fa12 = a.toFutureValue
              Pair(
                fa12.map(_._1).toValFrontier,
                fa12.map(_._2).toValFrontier,
              )                                                   .asInstanceOf[Frontier[B]]
          }

        case -⚬.UnliftPair() =>
          //          A          -⚬    B
          // (Val[X] |*| Val[Y]) -⚬ Val[(X, Y)]
          type X; type Y
          val (x, y) = Frontier.splitPair(this.asInstanceOf[Frontier[Val[X] |*| Val[Y]]])
          (x.toFutureValue zip y.toFutureValue).toValFrontier     .asInstanceOf[Frontier[B]]

        case -⚬.LiftNegPair() =>
          // Neg[(X, Y)] -⚬ (Neg[X] |*| Neg[Y])
          type X; type Y
          val px = Promise[X]()
          val py = Promise[Y]()
          this
            .asInstanceOf[Frontier[Neg[(X, Y)]]]
            .completeWith(px.future zip py.future)
          Pair(Prom(px), Prom(py))                                .asInstanceOf[Frontier[B]]

        case -⚬.UnliftNegPair() =>
          // (Neg[X] |*| Neg[Y]) -⚬ Neg[(A, B)]
          type X; type Y
          val p = Promise[(X, Y)]()
          val (nx, ny) = this.asInstanceOf[Frontier[Neg[X] |*| Neg[Y]]].splitPair
          nx.completeWith(p.future.map(_._1))
          ny.completeWith(p.future.map(_._2))
          Prom(p)                                                 .asInstanceOf[Frontier[B]]

        case -⚬.MapVal(f) =>
          type X; type Y
          this
            .asInstanceOf[Frontier[Val[X]]]
            .toFutureValue
            .map(f.asInstanceOf[X => Y])
            .toValFrontier                                        .asInstanceOf[Frontier[B]]

        case -⚬.ContramapNeg(f) =>
          this match {
            case Prom(pa) =>
              type B0
              val pb = Promise[B0]()
              pa.completeWith(pb.future.map(f.asInstanceOf[B0 => Nothing]))
              Prom(pb)                                            .asInstanceOf[Frontier[B]]
            case other =>
              bug(s"Did not expect $other to represent a Neg")
          }

        case -⚬.ConstVal(a) =>
          this
            .toFutureDone
            .map(_ => a)
            .toValFrontier

        case -⚬.ConstNeg(a) =>
          type X
          val pu = Promise[Any]()
          this
            .asInstanceOf[Frontier[Neg[X]]]
            .completeWith(pu.future.map(_ => a.asInstanceOf[X]))
          NeedAsync(pu)                                           .asInstanceOf[Frontier[B]]

        case -⚬.Neglect() =>
          type X
          this
            .asInstanceOf[Frontier[Val[X]]]
            .toFutureValue
            .map(_ => DoneNow)
            .asDeferredFrontier

        case -⚬.Inflate() =>
          // Need -⚬ Neg[X]
          type X
          val p = Promise[X]()
          this fulfillWith p.future
          Prom(p)                                                 .asInstanceOf[Frontier[B]]

        case -⚬.NotifyVal() =>
          // Val[X] -⚬ (Ping |*| Val[X])
          type X
          val (fd: Frontier[Ping], fx: Frontier[Val[X]]) =
            this.asInstanceOf[Frontier[Val[X]]] match {
              case x @ Value(_) =>
                (PingNow, x)
              case fx =>
                (fx.toFutureValue.map(_ => PingNow).asDeferredFrontier, fx)
            }
          Pair(fd, fx)                                            .asInstanceOf[Frontier[B]]

        case -⚬.NotifyNeg() =>
          // (Pong |*| Neg[X]) -⚬ Neg[X]
          type X
          val (n, x) = this.asInstanceOf[Frontier[Pong |*| Neg[X]]].splitPair
          n fulfillPongWith x.future
          x                                                       .asInstanceOf[Frontier[B]]

        case f @ -⚬.JoinRTermini() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case f @ -⚬.JoinLTermini() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case f @ -⚬.RInvertTerminus() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case f @ -⚬.LInvertTerminus() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case -⚬.Acquire(acquire0, release0) =>
          // Val[X] -⚬ (Res[R] |*| Val[Y])
          type X; type R; type Y

          val acquire: X => (R, Y) =
            acquire0.asInstanceOf
          val release: Option[R => Unit] =
            release0.asInstanceOf

          def go(x: X): Frontier[Res[R] |*| Val[Y]] = {
            def go1(r: R, y: Y): Frontier[Res[R] |*| Val[Y]] =
              release match {
                case None =>
                  Pair(MVal(r), Value(y))
                case Some(release) =>
                  resourceRegistry.registerResource(r, release andThen Async.now) match {
                    case RegisterResult.Registered(resId) =>
                      Pair(Resource(resId, r), Value(y))
                    case RegisterResult.RegistryClosed =>
                      release(r)
                      Frontier.failure("resource allocation not allowed because the program has ended or crashed")
                  }
              }

            val (r, y) = acquire(x)
            go1(r, y)
          }

          val res: Frontier[Res[R] |*| Val[Y]] =
            this.asInstanceOf[Frontier[Val[X]]] match {
              case Value(x) => go(x)
              case x => x.toFutureValue.map(go).asDeferredFrontier
            }

          res                                                     .asInstanceOf[Frontier[B]]

        case -⚬.TryAcquireAsync(acquire, release0) =>
          // Val[X] -⚬ (Val[E] |+| (Res[R] |*| Val[Y]))
          type X; type E; type R; type Y

          val release: Option[R => Async[Unit]] =
            release0.asInstanceOf

          def go(x: X): Frontier[Val[E] |+| (Res[R] |*| Val[Y])] = {
            def go1(res: Either[E, (R, Y)]): Frontier[Val[E] |+| (Res[R] |*| Val[Y])] =
              res match {
                case Left(e) =>
                  InjectL(Value(e))
                case Right((r, y)) =>
                  import ResourceRegistry.RegisterResult._
                  val fr: Frontier[Res[R] |*| Val[Y]] =
                    release match {
                      case None =>
                        Pair(MVal(r), Value(y))
                      case Some(release) =>
                        resourceRegistry.registerResource(r, release) match {
                          case Registered(resId) =>
                            Pair(Resource(resId, r), Value(y))
                          case RegistryClosed =>
                            release(r)
                              .map[Frontier[Res[R] |*| Val[Y]]](_ => Frontier.failure("resource allocation not allowed because the program has ended or crashed"))
                              .asAsyncFrontier
                        }
                      }
                  InjectR(fr)
              }

            acquire.asInstanceOf[X => Async[Either[E, (R, Y)]]](x) match {
              case Async.Now(value) => go1(value)
              case other => Async.toFuture(other).map(go1).asDeferredFrontier
            }
          }

          this.asInstanceOf[Frontier[Val[X]]] match {
            case Value(x) => go(x)                                .asInstanceOf[Frontier[B]]
            case x => x.toFutureValue.map(go).asDeferredFrontier  .asInstanceOf[Frontier[B]]
          }

        case -⚬.EffectAsync(f0) =>
          // (Res[R] |*| Val[X]) -⚬ (Res[R] |*| Val[Y])
          type R; type X; type Y

          val f: (R, X) => Async[Y] =
            f0.asInstanceOf

          def go(fr: ResFrontier[R], x: X): Frontier[Res[R] |*| Val[Y]] =
            fr match {
              case fr @ MVal(r) => f(r, x).map(y => Pair(fr, Value(y))).asAsyncFrontier
              case fr @ Resource(id, r) => f(r, x).map(y => Pair(fr, Value(y))).asAsyncFrontier
            }

          val res: Frontier[Res[R] |*| Val[Y]] =
            this.asInstanceOf[Frontier[Res[R] |*| Val[X]]].splitPair match {
              case (r: ResFrontier[R], Value(x)) => go(r, x)
              case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
            }

          res                                                     .asInstanceOf[Frontier[B]]

        case -⚬.EffectWrAsync(f0) =>
          // (Res[R] |*| Val[X]) -⚬ Res[R]
          type R; type X

          val f: (R, X) => Async[Unit] =
            f0.asInstanceOf

          def go(fr: ResFrontier[R], x: X): Frontier[Res[R]] =
            fr match {
              case fr @ MVal(r) => f(r, x).map(_ => fr).asAsyncFrontier
              case fr @ Resource(id, r) => f(r, x).map(_ => fr).asAsyncFrontier
            }

          val res: Frontier[Res[R]] =
            this.asInstanceOf[Frontier[Res[R] |*| Val[X]]].splitPair match {
              case (r: ResFrontier[R], Value(x)) => go(r, x)
              case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
            }

          res                                                     .asInstanceOf[Frontier[B]]

        case -⚬.TryTransformResourceAsync(f0, release0) =>
          // (Res[R] |*| Val[X]) -⚬ (Val[E] |+| (Res[S] |*| Val[Y]))
          type R; type X; type E; type S; type Y

          val f: (R, X) => Async[Either[E, (S, Y)]] =
            f0.asInstanceOf
          val release: Option[S => Async[Unit]] =
            release0.asInstanceOf

          def go(r: ResFrontier[R], x: X): Frontier[Val[E] |+| (Res[S] |*| Val[Y])] = {
            def go1(r: R, x: X): Frontier[Val[E] |+| (Res[S] |*| Val[Y])] =
              f(r, x)
                .map[Frontier[Val[E] |+| (Res[S] |*| Val[Y])]] {
                  case Left(e) =>
                    InjectL(Value(e))
                  case Right((s, y)) =>
                    val sy: Frontier[Res[S] |*| Val[Y]] =
                      release match {
                        case None =>
                          Pair(MVal(s), Value(y))
                        case Some(release) =>
                          resourceRegistry.registerResource(s, release) match {
                            case RegisterResult.Registered(id) =>
                              Pair(Resource(id, s), Value(y))
                            case RegisterResult.RegistryClosed =>
                              release(s)
                                .map(_ => Frontier.failure("Transformed resource not registered because shutting down"))
                                .asAsyncFrontier
                          }
                      }
                    InjectR(sy)
                }
                .asAsyncFrontier

            r match {
              case MVal(r) =>
                go1(r, x)
              case Resource(id, r) =>
                resourceRegistry.unregisterResource(id) match {
                  case UnregisterResult.Unregistered(_) =>
                    go1(r, x)
                  case UnregisterResult.NotFound =>
                    bug(s"Previously registered resource $id not found in resource registry")
                  case UnregisterResult.RegistryClosed =>
                    Frontier.failure("Not transforming resource because shutting down")
                }
            }
          }

          val res: Frontier[Val[E] |+| (Res[S] |*| Val[Y])] =
            this.asInstanceOf[Frontier[Res[R] |*| Val[X]]].splitPair match {
              case (r: ResFrontier[R], Value(x)) => go(r, x)
              case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
            }

          res                                                     .asInstanceOf[Frontier[B]]

        case -⚬.TrySplitResourceAsync(f0, rel1, rel2) =>
          // (Res[R] |*| Val[X]) -⚬ (Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[Y]))
          type R; type X; type E; type S; type T; type Y

          val f: (R, X) => Async[Either[E, (S, T, Y)]] =
            f0.asInstanceOf
          val releaseS: Option[S => Async[Unit]] =
            rel1.asInstanceOf
          val releaseT: Option[T => Async[Unit]] =
            rel2.asInstanceOf

          def go(r: ResFrontier[R], x: X): Frontier[Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[Y])] = {
            def go1(r: R, x: X): Frontier[Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[Y])] =
              f(r, x)
                .map[Frontier[Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[Y])]] {
                  case Left(e) =>
                    InjectL(Value(e))
                  case Right((s, t, y)) =>
                    val fs: Frontier[Res[S]] =
                      releaseS match {
                        case None =>
                          MVal(s)
                        case Some(releaseS) =>
                          resourceRegistry.registerResource(s, releaseS) match {
                            case RegisterResult.Registered(id) =>
                              Resource(id, s)
                            case RegisterResult.RegistryClosed =>
                              releaseS(s)
                                .map(_ => Frontier.failure("Post-split resource not registered because shutting down"))
                                .asAsyncFrontier
                          }
                      }
                    val ft: Frontier[Res[T]] =
                      releaseT match {
                        case None =>
                          MVal(t)
                        case Some(releaseT) =>
                          resourceRegistry.registerResource(t, releaseT) match {
                            case RegisterResult.Registered(id) =>
                              Resource(id, t)
                            case RegisterResult.RegistryClosed =>
                              releaseT(t)
                                .map(_ => Frontier.failure("Post-split resource not registered because shutting down"))
                                .asAsyncFrontier
                          }
                      }
                    InjectR(Pair(Pair(fs, ft), Value(y)))
                }
                .asAsyncFrontier

            r match {
              case MVal(r) =>
                go1(r, x)
              case Resource(id, r) =>
                resourceRegistry.unregisterResource(id) match {
                  case UnregisterResult.Unregistered(_) =>
                    go1(r, x)
                  case UnregisterResult.NotFound =>
                    bug(s"Previously registered resource $id not found in resource registry")
                  case UnregisterResult.RegistryClosed =>
                    Frontier.failure("Not going to split the resource because shutting down")
                }
            }
          }

          val res: Frontier[Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[Y])] =
            this.asInstanceOf[Frontier[Res[R] |*| Val[X]]].splitPair match {
              case (r: ResFrontier[R], Value(x)) => go(r, x)
              case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
            }

          res                                                     .asInstanceOf[Frontier[B]]

        case -⚬.ReleaseAsync(release0) =>
          // (Res[R] |*| Val[X]) -⚬ Val[Y]
          type R; type X; type Y

          val release: (R, X) => Async[Y] =
            release0.asInstanceOf

          def go(r: ResFrontier[R], x: X): Frontier[Val[Y]] =
            r match {
              case MVal(r) =>
                release(r, x).map(Value(_)).asAsyncFrontier
              case Resource(id, r) =>
                resourceRegistry.unregisterResource(id) match {
                  case UnregisterResult.Unregistered(_) =>
                    release(r, x).map(Value(_)).asAsyncFrontier
                  case UnregisterResult.NotFound =>
                    bug(s"Previously registered resource $id not found in resource registry")
                  case UnregisterResult.RegistryClosed =>
                    Frontier.failure("Not releasing resource because shutting down. It was or will be released as part of the shutdown")
                }
            }

          val res: Frontier[Val[Y]] =
            this.asInstanceOf[Frontier[Res[R] |*| Val[X]]].splitPair match {
              case (r: ResFrontier[R], Value(x)) => go(r, x)
              case (r, x) => (r.toFutureRes zipWith x.toFutureValue)(go).asDeferredFrontier
            }

          res                                                     .asInstanceOf[Frontier[B]]

        case -⚬.Release() =>
          // Res[R] -⚬ Done
          type R

          def go(r: ResFrontier[R]): Frontier[Done] =
            r match {
              case MVal(r) =>
                // no release needed, done
                DoneNow
              case Resource(id, r) =>
                resourceRegistry.unregisterResource(id) match {
                  case UnregisterResult.Unregistered(r) =>
                    r.releaseAsync(r.resource).map(_ => DoneNow).asAsyncFrontier
                  case UnregisterResult.NotFound =>
                    bug(s"Previously registered resource $id not found in resource registry")
                  case UnregisterResult.RegistryClosed =>
                    Frontier.failure("Not releasing resource because shutting down. It was or will be released as part of the shutdown")
                }
            }

          val res: Frontier[Done] =
            this.asInstanceOf[Frontier[Res[R]]] match {
              case r: ResFrontier[R] => go(r)
              case r => r.toFutureRes.map(go).asDeferredFrontier
            }

          res                                                     .asInstanceOf[Frontier[B]]

        case -⚬.Blocking(f0) =>
          // Val[X] -⚬ Val[Y]
          type X; type Y

          val f: X => Y =
            f0.asInstanceOf

          def go(x: X): Frontier[Val[Y]] = {
            val py = Promise[Y]()

            blockingExecutor.execute { () =>
              py.complete(Try(f(x)))
            }

            py.future.toValFrontier
          }

          val res: Frontier[Val[Y]] =
            this.asInstanceOf[Frontier[Val[X]]] match {
              case Value(x) => go(x)
              case other => other.toFutureValue.map(go).asDeferredFrontier
            }

          res                                                     .asInstanceOf[Frontier[B]]

        case -⚬.Backvert() =>
          // (X |*| -[X]) -⚬ One
          type X

          val (fw, bw) = this.asInstanceOf[Frontier[X |*| -[X]]].splitPair
          bw.fulfill(fw)
          One

        case -⚬.Forevert() =>
          // One -⚬ (-[X] |*| X)

          def go[X]: Frontier[-[X] |*| X] = {
            val pfx = Promise[Frontier[X]]()
            Pair(
              Backwards(pfx),
              Deferred(pfx.future),
            )
          }

          type X
          go[X]                                                   .asInstanceOf[Frontier[B]]
      }
    }

    private def crash(e: Throwable): Unit = {
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
        case Choice(_, _, onError) =>
          onError(e)
        case Deferred(fa) =>
          fa.map(_.crash(e))
        case Pack(f) =>
          f.crash(e)
        case Prom(promise) =>
          promise.failure(e)
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
    case class Choice[A, B](a: () => Frontier[A], b: () => Frontier[B], onError: Throwable => Unit) extends Frontier[A |&| B]
    case class Deferred[A](f: Future[Frontier[A]]) extends Frontier[A]
    case class Pack[F[_]](f: Frontier[F[Rec[F]]]) extends Frontier[Rec[F]]

    case class Value[A](a: A) extends Frontier[Val[A]]
    case class Prom[A](p: Promise[A]) extends Frontier[Neg[A]]

    sealed trait ResFrontier[A] extends Frontier[Res[A]]
    case class MVal[A](value: A) extends ResFrontier[A]
    case class Resource[A](id: ResId, obj: A) extends ResFrontier[A]

    case class Backwards[A](promise: Promise[Frontier[A]]) extends Frontier[-[A]]

    def failure[A](msg: String): Frontier[A] =
      Deferred(Future.failed(new Exception(msg)))

    extension (n: Frontier[Need]) {
      def fulfillWith(f: Future[Any]): Unit =
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
      def fulfillPongWith(f: Future[Any]): Unit =
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
      def futureEither: Future[Either[Frontier[A], Frontier[B]]] =
        f match {
          case InjectL(a) => Future.successful(Left(a))
          case InjectR(b) => Future.successful(Right(b))
          case Deferred(fab) => fab.flatMap(_.futureEither)
        }
    }

    extension [A, B](f: Frontier[A |&| B]) {
      def chooseL: Frontier[A] =
        f match {
          case Choice(a, b, onError) => a()
          case Deferred(f) => Deferred(f.map(_.chooseL))
        }

      def chooseR: Frontier[B] =
        f match {
          case Choice(a, b, onError) => b()
          case Deferred(f) => Deferred(f.map(_.chooseR))
        }

      def asChoice: Choice[A, B] =
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
      def splitPair: (Frontier[A], Frontier[B]) =
        f match {
          case Pair(a, b) => (a, b)
          case Deferred(f) =>
            val fab = f.map(_.splitPair)
            (Deferred(fab.map(_._1)), Deferred(fab.map(_._2)))
        }
    }

    extension (f: Frontier[Done]) {
      def toFutureDone: Future[DoneNow.type] =
        f match {
          case DoneNow =>
            Future.successful(DoneNow)
          case Deferred(f) =>
            f.flatMap(_.toFutureDone)
        }
    }

    extension (f: Frontier[Ping]) {
      def toFuturePing: Future[PingNow.type] =
        f match {
          case PingNow =>
            Future.successful(PingNow)
          case Deferred(f) =>
            f.flatMap(_.toFuturePing)
        }
    }

    extension [A](f: Frontier[Val[A]]) {
      def toFutureValue: Future[A] =
        f match {
          case Value(a) => Future.successful(a)
          case Deferred(fa) => fa.flatMap(_.toFutureValue)
        }
    }

    extension [A](f: Frontier[Res[A]]) {
      def toFutureRes: Future[ResFrontier[A]] =
        f match {
          case f @ MVal(_) => Future.successful(f)
          case f @ Resource(_, _) => Future.successful(f)
          case Deferred(f) => f.flatMap(_.toFutureRes)
        }
    }

    // using implicit class because extension methods may not have type parameters
    implicit class FrontierValOps[A](f: Frontier[Val[A]]) {
      def mapVal[B](g: A => B): Frontier[Val[B]] =
        f match {
          case Value(a) => Value(g(a))
          case Deferred(fa) => Deferred(fa.map(_.mapVal(g)))
        }
    }

    extension [A](f: Frontier[Neg[A]]) {
      def completeWith(fa: Future[A]): Unit =
        f match {
          case Prom(pa) => pa.completeWith(fa)
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

      def future: Future[A] =
        f match {
          case Prom(pa) => pa.future
          case Deferred(f) => f.flatMap(_.future)
        }
    }

    extension (f: Frontier[One]) {
      def awaitIfDeferred: Unit =
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
      def fulfill(fa: Frontier[A]): Unit =
        fna match {
          case Backwards(pfa) =>
            pfa.success(fa)
          case Deferred(ffna) =>
            ffna.onComplete {
              case Success(fna) => fna.fulfill(fa)
              case Failure(e) => e.printStackTrace(System.err)
            }
        }
    }

    extension [A](fa: Future[A]) {
      def toValFrontier: Frontier[Val[A]] =
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

  private class ResourceRegistry {
    import ResourceRegistry._

    // negative value indicates registry closed
    private var lastResId: Long =
      0L

    private val resourceMap: mutable.Map[Long, AcquiredResource[_]] =
      mutable.Map()

    def registerResource[R](resource: R, releaseAsync: R => Async[Unit]): RegisterResult =
      synchronized {
        if (lastResId < 0L) {
          assert(resourceMap.isEmpty)
          RegisterResult.RegistryClosed
        } else {
          lastResId += 1
          val id = lastResId
          resourceMap.put(id, AcquiredResource(resource, releaseAsync))
          RegisterResult.Registered(resId(id))
        }
      }

    def unregisterResource(id: ResId): UnregisterResult =
      synchronized {
        if (lastResId < 0l) {
          assert(resourceMap.isEmpty)
          UnregisterResult.RegistryClosed
        } else {
          resourceMap.remove(id.value) match {
            case None => UnregisterResult.NotFound
            case Some(r) => UnregisterResult.Unregistered(r)
          }
        }
      }

    def close(): Seq[AcquiredResource[_]] =
      synchronized {
        if (lastResId < 0L) {
          assert(resourceMap.isEmpty)
          Seq.empty
        } else {
          lastResId = Long.MinValue
          val result = resourceMap.values.toSeq
          resourceMap.clear()
          result
        }
      }
  }

  private object ResourceRegistry {
    opaque type ResId = Long
    private def resId(value: Long): ResId = value
    extension (resId: ResId) {
      def value: Long = resId
    }

    sealed trait RegisterResult
    object RegisterResult {
      case class Registered(id: ResId) extends RegisterResult
      case object RegistryClosed extends RegisterResult
    }

    sealed trait UnregisterResult
    object UnregisterResult {
      case class Unregistered(value: AcquiredResource[_]) extends UnregisterResult
      case object NotFound extends UnregisterResult
      case object RegistryClosed extends UnregisterResult
    }

    case class AcquiredResource[A](resource: A, releaseAsync: A => Async[Unit])
  }

  private case class Crash(msg: String) extends Exception(msg)
}
