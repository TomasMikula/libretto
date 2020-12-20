package libretto.impl

import libretto.ScalaRunner
import scala.concurrent.{ExecutionContext, Future, Promise}

/** Runner of [[FreeScalaDSL]] that returns a [[Future]].
  * 
  * It is known to be flawed by design in that it might create long (potentially infinite) chains of [[Promise]]s.
  * This could be solved with a custom implementation of promises/futures that support unregistration of listeners.
  * 
  * On top of that, expect bugs, since the implementation is full of unsafe type casts, because Scala's (including
  * Dotty's) type inference cannot cope with the kind of pattern matches found here.
  */
class FreeScalaFutureRunner(implicit ec: ExecutionContext) extends ScalaRunner[FreeScalaDSL.type, Future] {
  val dsl = FreeScalaDSL
  
  import dsl._
  
  private def bug[A](msg: String): A =
    throw new AssertionError(
      s"""$msg
         |This is a bug, please report at https://github.com/TomasMikula/libretto/issues/new?labels=bug"""
        .stripMargin
    )

  override def runScala[A](prg: One -⚬ Val[A]): Future[A] =
    Frontier.One.extendBy(prg).getFuture
  
  private sealed trait Frontier[A] {
    import Frontier._
    
    def extendBy[B](f: A -⚬ B): Frontier[B] =
      f match {
        case -⚬.Id() =>
          this
        case -⚬.AndThen(f, g) =>
          extendBy(f).extendBy(g)
        case -⚬.Par(f, g) =>
          this match {
            case other =>
              bug(s"Did not expect $other to represent a pair (? |*| ?).")
          }
        case -⚬.IntroFst() =>
          Pair(One, this)
        case -⚬.IntroSnd() =>
          Pair(this, One)
        case -⚬.ElimFst() =>
          this match {
            case Pair(_, b) => b                                  .asInstanceOf[Frontier[B]]
          }
        case -⚬.ElimSnd() =>
          this match {
            case Pair(a, _) => a                                  .asInstanceOf[Frontier[B]]
          }
        case -⚬.TimesAssocLR() =>
          this match {
            case Pair(Pair(a, b), c) => Pair(a, Pair(b, c))       .asInstanceOf[Frontier[B]]
          }
        case -⚬.TimesAssocRL() =>
          this match {
            case Pair(a, Pair(b, c)) => Pair(Pair(a, b), c)       .asInstanceOf[Frontier[B]]
          }
        case -⚬.Swap() =>
          this match {
            case Pair(a, b) => Pair(b, a)                         .asInstanceOf[Frontier[B]]
          }
        case -⚬.InjectL() =>
          InjectL(this)                                           .asInstanceOf[Frontier[B]]
        case -⚬.InjectR() =>
          InjectR(this)                                           .asInstanceOf[Frontier[B]]
        case -⚬.EitherF(f, g) =>
          this match {
            case InjectL(e) =>
              type A1
              e.asInstanceOf[Frontier[A1]].extendBy(f.asInstanceOf[A1 -⚬ B])
            case InjectR(e) =>
              type A2
              e.asInstanceOf[Frontier[A2]].extendBy(g.asInstanceOf[A2 -⚬ B])
          }
        case -⚬.ChooseL() =>
          this match {
            case Choice(f, g) => f()                              .asInstanceOf[Frontier[B]]
          }
        case -⚬.ChooseR() =>
          this match {
            case Choice(f, g) => g()                              .asInstanceOf[Frontier[B]]
          }
        case -⚬.Choice(f, g) =>
          Choice(
            () => this.extendBy(f),
            () => this.extendBy(g),
          )
        case -⚬.DoneF() =>
          // Ignore `this`. It ends in `One`, so it does not need to be taken care of.
          DoneNow                                                 .asInstanceOf[Frontier[B]]
        case -⚬.NeedF() =>
          this match {
            case NeedAsync(f) => f.success(())
          }
          One                                                     .asInstanceOf[Frontier[B]]
        case -⚬.DelayIndefinitely() =>
          ???
        case -⚬.RegressInfinitely() =>
          ???
        case -⚬.Fork() =>
          Pair(this, this)                                        .asInstanceOf[Frontier[B]]
        case -⚬.Join() =>
          this match {
            case Pair(DoneNow, DoneNow) => DoneNow                .asInstanceOf[Frontier[B]]
            case Pair(DoneNow, d2: DoneAsync) => d2               .asInstanceOf[Frontier[B]]
            case Pair(d1: DoneAsync, DoneNow) => d1               .asInstanceOf[Frontier[B]]
            case Pair(DoneAsync(f1), DoneAsync(f2)) =>
              DoneAsync((f1 zip f2).map(_ => ()))                 .asInstanceOf[Frontier[B]]
          }
        case -⚬.ForkNeed() =>
          this match {
            case NeedAsync(p) =>
              val p1 = Promise[Unit]().completeWith(p.future)
              val p2 = Promise[Unit]().completeWith(p.future)
              Pair(NeedAsync(p1), NeedAsync(p2))                  .asInstanceOf[Frontier[B]]
          }
        case -⚬.JoinNeed() =>
          this match {
            case NeedAsync(p) =>
              val p1 = Promise[Unit]()
              val p2 = Promise[Unit]()
              p.completeWith((p1.future zip p2.future).map(_ => ()))
              Pair(NeedAsync(p1), NeedAsync(p2))                  .asInstanceOf[Frontier[B]]
          }
        case -⚬.SignalEither() =>
          ???
        case -⚬.SignalChoice() =>
          ???
        case -⚬.InjectLWhenDone() =>
          ???
        case -⚬.InjectRWhenDone() =>
          ???
        case -⚬.ChooseLWhenNeed() =>
          ???
        case -⚬.ChooseRWhenNeed() =>
          ???
        case -⚬.DistributeLR() =>
          this match {
            case Pair(a, InjectL(f)) => InjectL(Pair(a, f))       .asInstanceOf[Frontier[B]]
            case Pair(a, InjectR(g)) => InjectR(Pair(a, g))       .asInstanceOf[Frontier[B]]
            case Pair(a, AsyncEither(f)) => AsyncEither(f.map {
              case Left(b) => Left(Pair(a, b))
              case Right(c) => Right(Pair(a, c))
            })                                                    .asInstanceOf[Frontier[B]]
          }
        case -⚬.CoDistributeL() =>
          // ((X |*| Y) |&| (X |*| Z)) -⚬ (X |*| (Y |&| Z))
          this match {
            case Choice(f, g) =>
              type X; type Y; type Z
              val px = Promise[Frontier[X]]()
              val chooseL: () => Frontier[Y] = { () =>
                f() match {
                  case Pair(a, b) => px.success(a.asInstanceOf[Frontier[X]]); b.asInstanceOf[Frontier[Y]]
                }
              }
              val chooseR: () => Frontier[Z] = { () =>
                g() match {
                  case Pair(a, c) => px.success(a.asInstanceOf[Frontier[X]]); c.asInstanceOf[Frontier[Z]]
                }
              }
              Pair(Deferred(px.future), Choice(chooseL, chooseR)) .asInstanceOf[Frontier[B]]
          }
        case -⚬.RInvertSignal() =>
          this match {
            case Pair(done, NeedAsync(p)) =>
              done match {
                case DoneNow => p.success(())
                case DoneAsync(f) => p.completeWith(f)
              }
              One                                                 .asInstanceOf[Frontier[B]]
          }
        case -⚬.LInvertSignal() =>
          this match {
            case One => 
              val p = Promise[Unit]()
              Pair(NeedAsync(p), DoneAsync(p.future))             .asInstanceOf[Frontier[B]]
          }
        case r @ -⚬.RecF(_) =>
          this.extendBy(r.recursed)
        case -⚬.Pack() =>
          type F[_]
          Pack(this.asInstanceOf[Frontier[F[Rec[F]]]])            .asInstanceOf[Frontier[B]]
        case -⚬.Unpack() =>
          this match {
            case Pack(f) => f                                     .asInstanceOf[Frontier[B]]
          }
        case -⚬.RaceCompletion() =>
          ???
        case -⚬.SelectRequest() =>
          ???
        case -⚬.Promise() =>
          this match {
            case One =>
              type X
              val px = Promise[X]()
              Pair(Prom(px), Fut(px.future))                      .asInstanceOf[Frontier[B]]
          }
        case -⚬.Fulfill() =>
          this match {
            case Pair(Fut(fa), Prom(pa)) =>
              type X
              val px = pa.asInstanceOf[Promise[X]]
              val fx = fa.asInstanceOf[Future[X]]
              px.completeWith(fx)
              One                                                 .asInstanceOf[Frontier[B]]
          }
        case -⚬.LiftEither() =>
          ???
        case -⚬.UnliftEither() =>
          ???
        case -⚬.LiftPair() =>
          ???
        case -⚬.UnliftPair() =>
          ???
        case -⚬.LiftNegPair() =>
          ???
        case -⚬.UnliftNegPair() =>
          ???
        case -⚬.LiftV(f) =>
          ???
        case -⚬.LiftN(f) =>
          ???
        case -⚬.ConstVal(a) =>
          this match {
            case DoneNow => Fut(Future.successful(a))             .asInstanceOf[Frontier[B]]
            case DoneAsync(f) => Fut(f.map(_ => a))               .asInstanceOf[Frontier[B]]
          }
        case -⚬.ConstNeg(a) =>
          this match {
            case Prom(pa) =>
              val pu = Promise[Unit]()
              pa.completeWith(pu.future.map(_ => a).asInstanceOf[Future[Nothing]])
              NeedAsync(pu)                                       .asInstanceOf[Frontier[B]]
          }
        case -⚬.Neglect() =>
          ???
        case -⚬.Inflate() =>
          ???
      }
      
    def getFuture[R](implicit ev: A =:= Val[R]): Future[R] = {
      val self: Frontier[Val[R]] = ev.substituteCo(this)
      self match {
        case Fut(f) => f
        case other => bug(s"Did not expect $other to represent Val[?].")
      }
    }
  }
  
  private object Frontier {
    case object One extends Frontier[dsl.One]
    case object DoneNow extends Frontier[Done]
    case class DoneAsync(future: Future[Unit]) extends Frontier[Done]
    case class NeedAsync(promise: Promise[Unit]) extends Frontier[Need]
    case class Pair[A, B](a: Frontier[A], b: Frontier[B]) extends Frontier[A |*| B]
    case class InjectL[A, B](a: Frontier[A]) extends Frontier[A |+| B]
    case class InjectR[A, B](b: Frontier[B]) extends Frontier[A |+| B]
    case class AsyncEither[A, B](f: Future[Either[Frontier[A], Frontier[B]]]) extends Frontier[A |+| B]
    case class Choice[A, B](a: () => Frontier[A], b: () => Frontier[B]) extends Frontier[A |&| B]
    case class Deferred[A](f: Future[Frontier[A]]) extends Frontier[A]
    case class Pack[F[_]](f: Frontier[F[Rec[F]]]) extends Frontier[Rec[F]]
    
    case class Fut[A](f: Future[A]) extends Frontier[Val[A]]
    case class Prom[A](p: Promise[A]) extends Frontier[Neg[A]]
  }
}
