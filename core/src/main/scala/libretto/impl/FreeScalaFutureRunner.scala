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

  override def runScala[A](prg: One -⚬ Val[A]): Future[A] = {
    import Frontier._
    val resourceRegistry = new ResourceRegistry
    val fa = Frontier.One.extendBy(prg, resourceRegistry).toFutureValue

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

        case -⚬.EitherF(f, g) =>
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

        case -⚬.Choice(f, g) =>
          Choice(
            () => this.extend(f),
            () => this.extend(g),
            onError = this.crash(_),
          )

        case -⚬.DoneF() =>
          // Ignore `this`. It ends in `One`, so it does not need to be taken care of.
          DoneNow                                                 .asInstanceOf[Frontier[B]]

        case -⚬.NeedF() =>
          this
            .asInstanceOf[Frontier[Need]]
            .fulfillWith(Future.successful(()))
          One                                                     .asInstanceOf[Frontier[B]]

        case f @ -⚬.DelayIndefinitely() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case f @ -⚬.RegressInfinitely() =>
          bug(s"Did not expect to be able to construct a program that uses $f")

        case -⚬.Fork() =>
          Pair(this, this)                                        .asInstanceOf[Frontier[B]]

        case -⚬.SignalDoneL() =>
          // Done -⚬ (WeakDone |*| Done)
          val d: Frontier[Done] = this.asInstanceOf
          val wd: Frontier[WeakDone] = d match {
            case DoneNow => WeakDoneNow
            case d => d.toFutureDone.map(_ => WeakDoneNow).asDeferredFrontier
          }
          Pair(wd, d)                                             .asInstanceOf[Frontier[B]]

        case -⚬.Join() =>
          def go(f1: Frontier[Done], f2: Frontier[Done]): Frontier[Done] =
            (f1, f2) match {
              case (DoneNow, d2) => d2
              case (d1, DoneNow) => d1
              case (Deferred(f1), Deferred(f2)) =>
                Deferred((f1 zipWith f2)(go))
            }
          val (d1, d2) = Frontier.splitPair(this.asInstanceOf[Frontier[Done |*| Done]])
          go(d1, d2)                                              .asInstanceOf[Frontier[B]]

        case -⚬.ForkNeed() =>
          val p = Promise[Any]()
          val (n1, n2) = this.asInstanceOf[Frontier[Need |*| Need]].splitPair
          n1 fulfillWith p.future
          n2 fulfillWith p.future
          NeedAsync(p)                                            .asInstanceOf[Frontier[B]]

        case -⚬.SignalNeedL() =>
          // (WeakNeed |*| Need) -⚬ Need
          val (wn, n) = this.asInstanceOf[Frontier[WeakNeed |*| Need]].splitPair
          val p = Promise[Any]()
          wn fulfillWeakWith p.future
          n fulfillWith p.future
          NeedAsync(p)                                            .asInstanceOf[Frontier[B]]

        case -⚬.JoinNeed() =>
          val p1 = Promise[Any]()
          val p2 = Promise[Any]()
          this
            .asInstanceOf[Frontier[Need]]
            .fulfillWith(p1.future zip p2.future)
          Pair(NeedAsync(p1), NeedAsync(p2))                      .asInstanceOf[Frontier[B]]

        case -⚬.SignalEither() =>
          type X; type Y
          this.asInstanceOf[Frontier[X |+| Y]] match {
            case l @ InjectL(_) => Pair(DoneNow, l)               .asInstanceOf[Frontier[B]]
            case r @ InjectR(_) => Pair(DoneNow, r)               .asInstanceOf[Frontier[B]]
            case other =>
              val decided = other.futureEither.map(_ => DoneNow).asDeferredFrontier
              Pair(decided, other)                                .asInstanceOf[Frontier[B]]
          }

        case -⚬.SignalChoice() =>
          //        A             -⚬     B
          // (Need |*| (X |&| Y)) -⚬ (X |&| Y)
          type X; type Y
          this.asInstanceOf[Frontier[Need |*| (X |&| Y)]].splitPair match {
            case (n, c) =>
              Choice(
                () => {
                  n fulfillWith Future.successful(())
                  Frontier.chooseL(c)
                },
                () => {
                  n fulfillWith Future.successful(())
                  Frontier.chooseR(c)
                },
                onError = { e =>
                  n fulfillWith Future.failed(e)
                  c.asChoice.onError(e)
                },
              )                                                   .asInstanceOf[Frontier[B]]
          }

        case -⚬.InjectLWhenDone() =>
          // (Done |*| X) -⚬ ((Done |*| X) |+| Y)
          type X
          val (d, x) = this.asInstanceOf[Frontier[Done |*| X]].splitPair
            d match {
              case DoneNow =>
                InjectL(Pair(DoneNow, x))                         .asInstanceOf[Frontier[B]]
              case d =>
                d
                  .toFutureDone
                  .map { doneNow => InjectL(Pair(doneNow, x)) }
                  .asDeferredFrontier                             .asInstanceOf[Frontier[B]]
            }

        case -⚬.InjectRWhenDone() =>
          // (Done |*| Y) -⚬ (X |+| (Done |*| Y))
          type Y
          val (d, y) = this.asInstanceOf[Frontier[Done |*| Y]].splitPair
          d match {
            case DoneNow =>
              InjectR(Pair(DoneNow, y))                           .asInstanceOf[Frontier[B]]
            case d =>
              d
                .toFutureDone
                .map { doneNow => InjectR(Pair(doneNow, y)) }
                .asDeferredFrontier                               .asInstanceOf[Frontier[B]]
          }

        case -⚬.ChooseLWhenNeed() =>
          // ((Need |*| X) |&| Y) -⚬ (Need |*| X)
          type X; type Y
          val Choice(nx, y, onError) = this.asInstanceOf[Frontier[(Need |*| X) |&| Y]].asChoice
          val pn = Promise[Any]()
          val px = Promise[Frontier[X]]()
          pn.future.onComplete {
            case Failure(e) =>
              onError(e)
              px.failure(e)
            case Success(_) =>
              val (n, x) = nx().splitPair
              n fulfillWith Future.successful(())
              px.success(x)
          }
          Pair(NeedAsync(pn), Deferred(px.future))                .asInstanceOf[Frontier[B]]

        case -⚬.ChooseRWhenNeed() =>
          // (X |&| (Need |*| Y)) -⚬ (Need |*| Y)
          type X; type Y
          val Choice(x, ny, onError) = this.asInstanceOf[Frontier[X |&| (Need |*| Y)]].asChoice
          val pn = Promise[Any]()
          val py = Promise[Frontier[Y]]()
          pn.future.onComplete {
            case Failure(e) =>
              onError(e)
              py.failure(e)
            case Success(_) =>
              val (n, y) = ny().splitPair
              n fulfillWith Future.successful(())
              py.success(y)
          }
          Pair(NeedAsync(pn), Deferred(py.future))                .asInstanceOf[Frontier[B]]

        case -⚬.DistributeL() =>
          // (X |*| (Y |+| Z)) -⚬ ((X |*| Y) |+| (X |*| Z))
          type X; type Y; type Z
          this.asInstanceOf[Frontier[X |*| (Y |+| Z)]].splitPair match {
            case (x, InjectL(y)) => InjectL(Pair(x, y))           .asInstanceOf[Frontier[B]]
            case (x, InjectR(z)) => InjectR(Pair(x, z))           .asInstanceOf[Frontier[B]]
            case (x, fyz) =>
              fyz
                .futureEither
                .map[Frontier[(X |*| Y) |+| (X |*| Z)]] {
                  case Left(y) => InjectL(Pair(x, y))
                  case Right(z) => InjectR(Pair(x, z))
                }
                .asDeferredFrontier                               .asInstanceOf[Frontier[B]]
          }

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
          val (d, n) = this.asInstanceOf[Frontier[Done |*| Need]].splitPair
          n fulfillWith d.toFutureDone
          One                                                     .asInstanceOf[Frontier[B]]

        case -⚬.LInvertSignal() =>
          this.asInstanceOf[Frontier[One]].awaitIfDeferred
          val p = Promise[Any]()
          Pair(NeedAsync(p), Deferred(p.future.map(_ => DoneNow))).asInstanceOf[Frontier[B]]

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
          def go(x: Frontier[WeakDone], y: Frontier[WeakDone]): Frontier[One |+| One] =
            (x, y) match {
              case (WeakDoneNow, y) => InjectL(One) // y is ignored
              case (x, WeakDoneNow) => InjectR(One) // x is ignored
              case (x, y) =>
                // check the first one for completion in order to be (somewhat) left-biased
                val fx = x.toFutureWeakDone
                fx.value match {
                  case Some(res) =>
                    // x completed, y is ignored
                    res match {
                      case Success(WeakDoneNow) => InjectL(One)
                      case Failure(e)           => Deferred(Future.failed(e))
                    }
                  case None =>
                    val fy = y.toFutureWeakDone
                    val p = Promise[Frontier[One |+| One]]
                    fx.onComplete(r => p.tryComplete(r.map(_ => InjectL(One))))
                    fy.onComplete(r => p.tryComplete(r.map(_ => InjectR(One))))
                    Deferred(p.future)
                }
            }

          val (x, y) = this.asInstanceOf[Frontier[WeakDone |*| WeakDone]].splitPair
          go(x, y)                                                .asInstanceOf[Frontier[B]]

        case -⚬.RaceDone() =>
          val (x, y) = this.asInstanceOf[Frontier[Done |*| Done]].splitPair
          (x, y) match {
            case (DoneNow, y) => InjectL(y)                       .asInstanceOf[Frontier[B]]
            case (x, DoneNow) => InjectR(x)                       .asInstanceOf[Frontier[B]]
            case (x, y) =>
              // check the first for completion in order to be (somewhat) left-biased
              val fx = x.toFutureDone
              fx.value match {
                case Some(Success(DoneNow)) => InjectL(y)         .asInstanceOf[Frontier[B]]
                case Some(Failure(e))       => Deferred(Future.failed(e))
                case None =>
                  val fy = y.toFutureDone
                  val p = Promise[Frontier[Done |+| Done]]
                  fx.onComplete(r => p.tryComplete(r.map(_ => InjectL(y))))
                  fy.onComplete(r => p.tryComplete(r.map(_ => InjectR(x))))
                  Deferred(p.future)                              .asInstanceOf[Frontier[B]]
              }
          }

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
          Pair(WeakNeedAsync(p1), WeakNeedAsync(p2))              .asInstanceOf[Frontier[B]]

        case -⚬.SelectNeed() =>
          // XXX: not left-biased. What does it even mean, precisely, for a racing operator to be biased?
          val Choice(f, g, onError) = this.asInstanceOf[Frontier[Need |&| Need]].asChoice
          val p1 = Promise[Any]()
          val p2 = Promise[Any]()
          val p = Promise[(() => Frontier[Need], Future[Any])]
          p1.future.onComplete(r => p.tryComplete(r.map(_ => (f, p2.future))))
          p2.future.onComplete(r => p.tryComplete(r.map(_ => (g, p1.future))))
          p.future.onComplete {
            case Success((n, fut)) => n() fulfillWith fut
            case Failure(e) => onError(e)
          }
          Pair(NeedAsync(p1), NeedAsync(p2))                      .asInstanceOf[Frontier[B]]

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
          this
            .asInstanceOf[Frontier[Val[FiniteDuration]]]
            .toFutureValue
            .flatMap(d => schedule(d, () => DoneNow))
            .asDeferredFrontier                                   .asInstanceOf[Frontier[B]]

        case -⚬.Promise() =>
          this.asInstanceOf[Frontier[One]].awaitIfDeferred
          type X
          val px = Promise[X]()
          Pair(Prom(px), px.future.toValFrontier)                 .asInstanceOf[Frontier[B]]

        case -⚬.Fulfill() =>
          type X
          val (x, nx) = this.asInstanceOf[Frontier[Val[X] |*| Neg[X]]].splitPair
          nx.completeWith(x.toFutureValue)
          One                                                     .asInstanceOf[Frontier[B]]

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
            .asInstanceOf[Frontier[Done]]
            .toFutureDone
            .map(_ => a)
            .toValFrontier                                        .asInstanceOf[Frontier[B]]

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
            .asDeferredFrontier                                   .asInstanceOf[Frontier[B]]

        case -⚬.Inflate() =>
          // Need -⚬ Neg[X]
          type X
          val p = Promise[X]()
          this.asInstanceOf[Frontier[Need]] fulfillWith p.future
          Prom(p)                                                 .asInstanceOf[Frontier[B]]

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
      }
    }

    private def crash(e: Throwable): Unit = {
      this match {
        case One | DoneNow | WeakDoneNow | Value(_) | MVal(_) | Resource(_, _) =>
          // do nothing
        case NeedAsync(promise) =>
          promise.failure(e)
        case WeakNeedAsync(promise) =>
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
    case object WeakDoneNow extends Frontier[WeakDone]
    case class NeedAsync(promise: Promise[Any]) extends Frontier[Need]
    case class WeakNeedAsync(promise: Promise[Any]) extends Frontier[WeakNeed]
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

    extension (n: Frontier[WeakNeed]) {
      def fulfillWeakWith(f: Future[Any]): Unit =
        n match {
          case WeakNeedAsync(p) =>
            p.completeWith(f)
          case Deferred(fn) =>
            fn.onComplete {
              case Success(n) => n fulfillWeakWith f
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

    extension (f: Frontier[WeakDone]) {
      def toFutureWeakDone: Future[WeakDoneNow.type] =
        f match {
          case WeakDoneNow =>
            Future.successful(WeakDoneNow)
          case Deferred(f) =>
            f.flatMap(_.toFutureWeakDone)
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
