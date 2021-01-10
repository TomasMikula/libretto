package libretto.impl

import java.util.concurrent.{ScheduledExecutorService, TimeUnit}
import libretto.ScalaRunner
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
class FreeScalaFutureRunner(scheduler: ScheduledExecutorService) extends ScalaRunner[FreeScalaDSL.type, Future] {
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
    Frontier.One.extendBy(prg).toFutureValue
  }

  private sealed trait Frontier[A] {
    import Frontier._
    
    def extendBy[B](f: A -⚬ B): Frontier[B] = {
      f match {
        case -⚬.Id() =>
          this
        case -⚬.AndThen(f, g) =>
          extendBy(f).extendBy(g)
        case -⚬.Par(f, g) =>
          type A1; type A2
          val (a1, a2) = this.asInstanceOf[Frontier[A1 |*| A2]].splitPair
          Pair(
            a1.extendBy(f.asInstanceOf[A1 -⚬ Nothing]),
            a2.extendBy(g.asInstanceOf[A2 -⚬ Nothing]),
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
        case -⚬.TimesAssocLR() =>
          // ((X |*| Y) |*| Z) -⚬ (X |*| (Y |*| Z))
          type X; type Y
          this match {
            case Pair(xy, z) =>
              val (x, y) = Frontier.splitPair(xy.asInstanceOf[Frontier[X |*| Y]])
              Pair(x, Pair(y, z))                                 .asInstanceOf[Frontier[B]]
            case other =>
              bug(s"Did not expect $other to represent ((? |*| ?) |*| ?)")
          }
        case -⚬.TimesAssocRL() =>
          // (X |*| (Y |*| Z)) -⚬ ((X |*| Y) |*| Z)
          type Y; type Z
          this match {
            case Pair(x, yz) =>
              val (y, z) = Frontier.splitPair(yz.asInstanceOf[Frontier[Y |*| Z]])
              Pair(Pair(x, y), z)                                 .asInstanceOf[Frontier[B]]
            case other =>
              bug(s"Did not expect $other to represent (? |*| (? |*| ?))")
          }
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
                a1.extendBy(f.asInstanceOf[A1 -⚬ B])
              case InjectR(a2) =>
                a2.extendBy(g.asInstanceOf[A2 -⚬ B])
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
            () => this.extendBy(f),
            () => this.extendBy(g),
            onError = this.crash(_),
          )
        case -⚬.DoneF() =>
          // Ignore `this`. It ends in `One`, so it does not need to be taken care of.
          DoneNow                                                 .asInstanceOf[Frontier[B]]
        case -⚬.NeedF() =>
          Frontier.fulfillNeedWith(
            this.asInstanceOf[Frontier[Need]],
            Future.successful(()),
          )
          One                                                     .asInstanceOf[Frontier[B]]
        case -⚬.DelayIndefinitely() =>
          ???
        case -⚬.RegressInfinitely() =>
          ???
        case -⚬.Fork() =>
          Pair(this, this)                                        .asInstanceOf[Frontier[B]]
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
          this.asInstanceOf[Frontier[Need |*| Need]].splitPair match {
            case (n1, n2) =>
              Frontier.fulfillNeedWith(n1, p.future)
              Frontier.fulfillNeedWith(n2, p.future)
          }
          NeedAsync(p)                                            .asInstanceOf[Frontier[B]]
        case -⚬.JoinNeed() =>
          val p1 = Promise[Any]()
          val p2 = Promise[Any]()
          Frontier.fulfillNeedWith(
            this.asInstanceOf[Frontier[Need]],
            (p1.future zip p2.future),
          )
          Pair(NeedAsync(p1), NeedAsync(p2))                      .asInstanceOf[Frontier[B]]
        case -⚬.SignalEither() =>
          ???
        case -⚬.SignalChoice() =>
          //        A             -⚬     B
          // (Need |*| (X |&| Y)) -⚬ (X |&| Y)
          type X; type Y
          this.asInstanceOf[Frontier[Need |*| (X |&| Y)]].splitPair match {
            case (n, c) =>
              Choice(
                () => {
                  Frontier.fulfillNeedWith(n, Future.successful(()))
                  Frontier.chooseL(c)
                },
                () => {
                  Frontier.fulfillNeedWith(n, Future.successful(()))
                  Frontier.chooseR(c)
                },
                onError = { e =>
                  Frontier.fulfillNeedWith(n, Future.failed(e))
                  c.asChoice.onError(e)
                },
              )                                                   .asInstanceOf[Frontier[B]]
          }
        case -⚬.InjectLWhenDone() =>
          // (Done |*| X) -⚬ ((Done |*| X) |+| Y)
          type X
          this.asInstanceOf[Frontier[Done |*| X]].splitPair match {
            case (d, x) =>
              d match {
                case DoneNow =>
                  InjectL(Pair(DoneNow, x))                       .asInstanceOf[Frontier[B]]
                case Deferred(fut) =>
                  Deferred(fut.map(d => Pair(d, x).extendBy(-⚬.InjectLWhenDone())))
                                                                  .asInstanceOf[Frontier[B]]
              }
          }
        case -⚬.InjectRWhenDone() =>
          ???
        case -⚬.ChooseLWhenNeed() =>
          // ((Need |*| X) |&| Y) -⚬ (Need |*| X)
          type X
          this match {
            case Choice(nx, y, onError) =>
              val pn = Promise[Any]()
              val px = Promise[Frontier[X]]()
              pn.future.onComplete {
                case Failure(e) =>
                  onError(e)
                  px.failure(e)
                case Success(_) =>
                  val (n, x) = Frontier.splitPair(nx().asInstanceOf[Frontier[Need |*| X]])
                  Frontier.fulfillNeedWith(n, Future.successful(()))
                  px.success(x)
              }
              Pair(NeedAsync(pn), Deferred(px.future))            .asInstanceOf[Frontier[B]]
            case other =>
              bug(s"Did not expect $other to represent (? |&| ?)")
          }
        case -⚬.ChooseRWhenNeed() =>
          ???
        case -⚬.DistributeLR() =>
          // (X |*| (Y |+| Z)) -⚬ ((X |*| Y) |+| (X |*| Z))
          type X; type Y; type Z
          this.asInstanceOf[Frontier[X |*| (Y |+| Z)]].splitPair match {
            case (a, InjectL(f)) => InjectL(Pair(a, f))           .asInstanceOf[Frontier[B]]
            case (a, InjectR(g)) => InjectR(Pair(a, g))           .asInstanceOf[Frontier[B]]
            case (x, Deferred(fyz)) =>
              Deferred(fyz.map(yz =>
                Pair(x, yz)
                  .extendBy(-⚬.DistributeLR[X, Y, Z]())           .asInstanceOf[Frontier[B]]
              ))
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
          Frontier.fulfillNeedWith(n, d.toFutureDone)
          One                                                     .asInstanceOf[Frontier[B]]
        case -⚬.LInvertSignal() =>
          this.asInstanceOf[Frontier[One]].awaitIfDeferred
          val p = Promise[Any]()
          Pair(NeedAsync(p), Deferred(p.future.map(_ => DoneNow))).asInstanceOf[Frontier[B]]
        case r @ -⚬.RecF(_) =>
          this.extendBy(r.recursed)
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
        case -⚬.RaceCompletion() =>
          val (x, y) = this.asInstanceOf[Frontier[Done |*| Done]].splitPair
          (x, y) match {
            case (DoneNow, y) => InjectL(y)                       .asInstanceOf[Frontier[B]]
            case (x, DoneNow) => InjectR(x)                       .asInstanceOf[Frontier[B]]
            case (x, y) =>
              val d1 = x.asInstanceOf[Frontier[Done]]
              val d2 = y.asInstanceOf[Frontier[Done]]
              val p = Promise[Frontier[Done |+| Done]]
              d1.toFutureDone.onComplete(r => p.tryComplete(r.map(_ => InjectL(d2))))
              d2.toFutureDone.onComplete(r => p.tryComplete(r.map(_ => InjectR(d1))))
              Deferred(p.future)                                  .asInstanceOf[Frontier[B]]
          }
        case -⚬.SelectRequest() =>
          this.asInstanceOf[Frontier[Need |&| Need]].asChoice match {
            case Choice(f, g, onError) =>
              val p1 = Promise[Any]()
              val p2 = Promise[Any]()
              val p = Promise[(() => Frontier[Need], Future[Any])]
              p1.future.onComplete(r => p.tryComplete(r.map(_ => (f.asInstanceOf[() => Frontier[Need]], p2.future))))
              p2.future.onComplete(r => p.tryComplete(r.map(_ => (g.asInstanceOf[() => Frontier[Need]], p1.future))))
              p.future.onComplete {
                case Success((n, fut)) => Frontier.fulfillNeedWith(n(), fut)
                case Failure(e) => onError(e)
              }
              Pair(NeedAsync(p1), NeedAsync(p2))                  .asInstanceOf[Frontier[B]]
          }
        case -⚬.Crash(msg) =>
          val e = Crash(msg)
          this.crash(e)
          Deferred(Future.failed(e))
        case -⚬.Delay(d) =>
          this
            .asInstanceOf[Frontier[Done]]
            .toFutureDone
            .flatMap(doneNow => schedule(d, () => doneNow))
            .asDeferredFrontier                                   .asInstanceOf[Frontier[B]]
        case -⚬.Promise() =>
          this.asInstanceOf[Frontier[One]].awaitIfDeferred
          type X
          val px = Promise[X]()
          Pair(Prom(px), px.future.toValFrontier)                 .asInstanceOf[Frontier[B]]
        case -⚬.Fulfill() =>
          type X
          val (x, nx) = this.asInstanceOf[Frontier[Val[X] |*| Neg[X]]].splitPair
          nx.futurePromise.onComplete {
            case Success(px) => px.completeWith(x.toFutureValue)
            case Failure(e) =>
              e.printStackTrace(System.err)
              x.toFutureValue.onComplete {
                case Success(_) => // do nothing
                case Failure(e) => e.printStackTrace(System.err)
              }
          }
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
        case -⚬.UnliftEither() =>
          ???
        case -⚬.LiftPair() =>
          type A1; type A2 // such that A = Val[(A1, A2)]
          this match {
            case Value(a) =>
              val (a1, a2) = a.asInstanceOf[(A1, A2)]
              Pair(Value(a1), Value(a2))                          .asInstanceOf[Frontier[B]]
            case a =>
              val fa12 = a.asInstanceOf[Frontier[Val[(A1, A2)]]].toFutureValue
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
          ???
        case -⚬.UnliftNegPair() =>
          ???
        case -⚬.LiftV(f) =>
          type X; type Y
          this
            .asInstanceOf[Frontier[Val[X]]]
            .toFutureValue
            .map(f.asInstanceOf[X => Y])
            .toValFrontier                                        .asInstanceOf[Frontier[B]]
        case -⚬.LiftN(f) =>
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
            .futurePromise
            .zip(pu.future)
            .onComplete {
              case Success((px, _)) => px.success(a.asInstanceOf[X])
              case Failure(e) => e.printStackTrace(System.err)
            }
          NeedAsync(pu)                                           .asInstanceOf[Frontier[B]]
        case -⚬.Neglect() =>
          type X
          this
            .asInstanceOf[Frontier[Val[X]]]
            .toFutureValue
            .map(_ => DoneNow)
            .asDeferredFrontier                                   .asInstanceOf[Frontier[B]]
        case -⚬.Inflate() =>
          ???
        case -⚬.JoinRTermini() =>
          ???
        case -⚬.JoinLTermini() =>
          ???
        case -⚬.RInvertTerminus() =>
          ???
        case -⚬.LInvertTerminus() =>
          ???
      }
    }

    private def crash(e: Throwable): Unit = {
      this match {
        case One | DoneNow | Value(_) =>
          // do nothing
        case NeedAsync(promise) =>
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
    case class NeedAsync(promise: Promise[Any]) extends Frontier[Need]
    case class Pair[A, B](a: Frontier[A], b: Frontier[B]) extends Frontier[A |*| B]
    case class InjectL[A, B](a: Frontier[A]) extends Frontier[A |+| B]
    case class InjectR[A, B](b: Frontier[B]) extends Frontier[A |+| B]
    case class Choice[A, B](a: () => Frontier[A], b: () => Frontier[B], onError: Throwable => Unit) extends Frontier[A |&| B]
    case class Deferred[A](f: Future[Frontier[A]]) extends Frontier[A]
    case class Pack[F[_]](f: Frontier[F[Rec[F]]]) extends Frontier[Rec[F]]
    
    case class Value[A](a: A) extends Frontier[Val[A]]
    case class Prom[A](p: Promise[A]) extends Frontier[Neg[A]]
    
    def fulfillNeedWith(n: Frontier[Need], f: Future[Any]): Unit =
      n match {
        case NeedAsync(p) =>
          p.completeWith(f)
        case Deferred(fn) =>
          fn.onComplete {
            case Success(n) => fulfillNeedWith(n, f)
            case Failure(e) =>
              e.printStackTrace(System.err)
              f.onComplete {
                case Success(_) => // do nothing
                case Failure(ex) => ex.printStackTrace(System.err)
              }
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

    extension [A](f: Frontier[Val[A]]) {
      def toFutureValue: Future[A] =
        f match {
          case Value(a) => Future.successful(a)
          case Deferred(fa) => fa.flatMap(_.toFutureValue)
        }
    }

    extension [A](f: Frontier[Neg[A]]) {
      def futurePromise: Future[Promise[A]] =
        f match {
          case Prom(pa) => Future.successful(pa)
          case Deferred(fa) => fa.flatMap(_.futurePromise)
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
  }
  
  private case class Crash(msg: String) extends Exception(msg)
}
