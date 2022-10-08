package libretto.scaletto.impl.concurrentcells

import java.util.concurrent.atomic.AtomicReference
import libretto.scaletto.ScalettoExecution
import libretto.scaletto.impl.FreeScaletto
import libretto.util.Async
import libretto.Executor.CancellationReason
import libretto.Scheduler
import scala.concurrent.ExecutionContext

class ExecutionImpl(
  ec: ExecutionContext,
  scheduler: Scheduler,
) extends ScalettoExecution[FreeScaletto.type] {
  override val dsl = FreeScaletto

  import dsl._

  override type InPort[A] = Cell[A]
  override type OutPort[A] = Cell[A]

  override object InPort extends ScalettoInPorts {
    override def split[A, B](port: Cell[A |*| B]): (Cell[A], Cell[B]) = ???
    override def discardOne(port: Cell[One]): Unit = ???
    override def supplyDone(port: Cell[Done]): Unit = Cell.supplyDone(port).followUp()
    override def supplyPing(port: Cell[Ping]): Unit = ???
    override def supplyLeft[A, B](port: Cell[A |+| B]): Cell[A] = ???
    override def supplyRight[A, B](port: Cell[A |+| B]): Cell[B] = ???
    override def supplyChoice[A, B](port: Cell[A |&| B]): Async[Either[Throwable, Either[Cell[A], Cell[B]]]] = ???
    override def supplyVal[A](port: Cell[Val[A]], value: A): Unit = ???
    override def contramap[A, B](port: Cell[B])(f: A -⚬ B): Cell[A] = ???
    override def functionInputOutput[I, O](port: Cell[I =⚬ O]): (Cell[I], Cell[O]) = ???
  }

  override object OutPort extends ScalettoOutPorts {
    override def split[A, B](port: Cell[A |*| B]): (Cell[A], Cell[B]) = ???
    override def discardOne(port: Cell[One]): Unit = ???

    override def awaitDone(port: Cell[Done]): Async[Either[Throwable, Unit]] = {
      val (completer, async) = Async.promiseLinear[Either[Throwable, Unit]]
      Cell.awaitDone(port, completer).followUp()
      async
    }

    override def awaitPing(port: Cell[Ping]): Async[Either[Throwable, Unit]] = ???

    override def awaitEither[A, B](port: Cell[A |+| B]): Async[Either[Throwable, Either[Cell[A], Cell[B]]]] = {
      val (completer, async) = Async.promiseLinear[Either[Throwable, Either[Cell[A], Cell[B]]]]
      Cell.awaitEither(port, completer).followUp()
      async
    }

    override def chooseLeft[A, B](port: Cell[A |&| B]): Cell[A] = ???
    override def chooseRight[A, B](port: Cell[A |&| B]): Cell[B] = ???
    override def awaitVal[A](port: Cell[Val[A]]): Async[Either[Throwable, A]] = ???
    override def map[A, B](port: Cell[A])(f: A -⚬ B): Cell[B] = ???
    override def functionInputOutput[I, O](port: Cell[I =⚬ O]): (Cell[I], Cell[O]) = ???
  }

  enum CancellationState {
    case Initial
    case Cancelling
    case Cancelled
  }

  val cancellationState = new AtomicReference(CancellationState.Initial)

  val (notifyOnCancel, watchCancellation) =
    Async.promise[CancellationReason]

  def execute[A, B](prg: A -⚬ B): (InPort[A], OutPort[B]) = {
    val in = Cell.empty[A]
    val out = Cell.empty[B]
    submitJob { () => connect(in, prg, out) }
    (in, out)
  }

  def cancel(reason: CancellationReason): Async[Unit] = {
    import CancellationState._

    if (cancellationState.compareAndSet(Initial, Cancelling)) {
      Async
        .now(()) // TODO: release resources
        .map { _ =>
          cancellationState.compareAndSet(Cancelling, Cancelled)
          notifyOnCancel(reason)
        }
    } else {
      watchCancellation.map(_ => ())
    }
  }

  def watchForCancellation(): Async[CancellationReason] =
    watchCancellation

  private def submitJob(action: Runnable): Unit = {
    val safeAction: Runnable =
      () => {
        if (cancellationState.get() == CancellationState.Initial) {
          try  {
            action.run()
          } catch {
            e => cancel(CancellationReason.Bug("Job threw an exception", Some(e)))
          }
        }
      }

    ec.execute(safeAction)
  }

  private def connectLater[A, B](in: Cell[A], f: A -⚬ B, out: Cell[B]): Unit =
    submitJob { () => connect(in, f, out) }

  private def connect[A, B](in: Cell[A], f: A -⚬ B, out: Cell[B]): Unit =
    f match {
      case -⚬.Id() =>
        unify(in, out)

      case -⚬.AndThen(f, g) =>
        inline def go[X](f: A -⚬ X, g: X -⚬ B): Unit =
          val x = Cell.empty[X]
          connectLater(in, f, x)
          connectLater(x, g, out)

        go(f, g)

      case p: -⚬.Par[a1, b1, a2, b2] =>
        inline def go[A1, A2, B1, B2](
          in: Cell[A1 |*| A2],
          f1: A1 -⚬ B1,
          f2: A2 -⚬ B2,
          out: Cell[B1 |*| B2],
        ): Unit =
          val (a1, a2, r1) = Cell.rsplit(in)
          val (b1, b2, r2) = Cell.lsplit(out)
          connectLater(a1, f1, b1)
          connectLater(a2, f2, b2)
          r1.followUp()
          r2.followUp()

        go[a1, a2, b1, b2](in, p.f, p.g, out)

      case -⚬.IntroFst() =>
        inline def go(out: Cell[One |*| A]): Unit =
          val (_, out1, r) = Cell.lsplit(out)
          unify(in, out1)
          r.followUp()

        go(out)

      case -⚬.IntroSnd() =>
        inline def go(out: Cell[A |*| One]): Unit =
          val (out1, _, r) = Cell.lsplit(out)
          unify(in, out1)
          r.followUp()

        go(out)

      case -⚬.ElimFst() =>
        inline def go(in: Cell[One |*| B]): Unit =
          val (_, in1, r) = Cell.rsplit(in)
          unify(in1, out)
          r.followUp()

        go(in)

      case -⚬.ElimSnd() =>
        inline def go(in: Cell[B |*| One]): Unit =
          val (in1, _, r) = Cell.rsplit(in)
          unify(in1, out)
          r.followUp()

        go(in)

      case _: -⚬.AssocLR[x, y, z] =>
        inline def go[X, Y, Z](in: Cell[(X |*| Y) |*| Z], out: Cell[X |*| (Y |*| Z)]): Unit =
          val (ixy, iz, r1) = Cell.rsplit(in)
          val (ix, iy, r2)  = Cell.rsplit(ixy)
          val (ox, oyz, r3) = Cell.lsplit(out)
          val (oy, oz, r4)  = Cell.lsplit(oyz)
          unify(ix, ox)
          unify(iy, oy)
          unify(iz, oz)
          r1.followUp()
          r2.followUp()
          r3.followUp()
          r4.followUp()

        go[x, y, z](in, out)

      case _: -⚬.AssocRL[x, y, z] =>
        inline def go[X, Y, Z](in: Cell[X |*| (Y |*| Z)], out: Cell[(X |*| Y) |*| Z]): Unit =
          val (ix, iyz, r1) = Cell.rsplit(in)
          val (iy, iz, r2)  = Cell.rsplit(iyz)
          val (oxy, oz, r3) = Cell.lsplit(out)
          val (ox, oy, r4)  = Cell.lsplit(oxy)
          unify(ix, ox)
          unify(iy, oy)
          unify(iz, oz)
          r1.followUp()
          r2.followUp()
          r3.followUp()
          r4.followUp()

        go[x, y, z](in, out)

      case _: -⚬.Swap[x, y] =>
        inline def go[X, Y](in: Cell[X |*| Y], out: Cell[Y |*| X]): Unit =
          val (ix, iy, r1) = Cell.rsplit(in)
          val (oy, ox, r2) = Cell.lsplit(out)
          unify(ix, ox)
          unify(iy, oy)
          r1.followUp()
          r2.followUp()

        go[x, y](in, out)

      case _: -⚬.InjectL[x, y] =>
        Cell.injectL[x, y](in, out).followUp()

      case _: -⚬.InjectR[x, y] =>
        Cell.injectR[x, y](in, out).followUp()

      case e: -⚬.EitherF[x, y, z] =>
        Cell.either[x, y, z](in, e.f, e.g, out).followUp()

      case _: -⚬.ChooseL[l, r] =>
        Cell.chooseL[l, r](in, out).followUp()

      case _: -⚬.ChooseR[l, r] =>
        Cell.chooseR[l, r](in, out).followUp()

      case c: -⚬.Choice[a, b1, b2] =>
        Cell.choice[a, b1, b2](in, c.f, c.g, out).followUp()

      case _: -⚬.Join =>
        val (in1, in2, r) = Cell.rsplit[Done, Done](in)
        Cell.join(in1, in2, out).followUp()
        r.followUp()

      case _: -⚬.JoinPong =>
        val (out1, out2, r) = Cell.lsplit[Pong, Pong](out)
        Cell.joinPong(in, out1, out2).followUp()
        r.followUp()

      case r: -⚬.RecF[A, B] =>
        connect(in, r.recursed, out)

      case _: -⚬.Pack[f] =>
        def go[F[_]](in: Cell[F[Rec[F]]], out: Cell[Rec[F]]): Unit =
          val ev = summon[Rec[F] =:= Rec[F]].asInstanceOf[Rec[F] =:= F[Rec[F]]] // XXX: cheating
          unify(in, ev.substituteCo(out))

        go[f](in, out)

      case _: -⚬.Unpack[f] =>
        def go[F[_]](in: Cell[Rec[F]], out: Cell[F[Rec[F]]]): Unit =
          val ev = summon[Rec[F] =:= Rec[F]].asInstanceOf[Rec[F] =:= F[Rec[F]]] // XXX: cheating
          unify(in, ev.substituteContra(out))

        go[f](in, out)

      case _: -⚬.SelectPair =>
        val (o1, o2, r) = Cell.lsplit[Pong, Pong](out)
        Cell.select(in, o1, o2).followUp()
        r.followUp()

      case _: -⚬.CoDistributeL[x, y, z] =>
        val (ox, oyz, r) = Cell.lsplit[x, y |&| z](out)
        Cell.choiceWith[x, y, z](in, ox, oyz).followUp()
        r.followUp()

      case _: -⚬.RInvertSignal =>
        val (in1, in2, r) = Cell.rsplit[Done, Need](in)
        Cell.rInvertSignal(in1, in2).followUp()
        r.followUp()
        // `out: Cell[One]` can be ignored

      case _: -⚬.NotifyEither[x, y] =>
        val (o1, o2, r) = Cell.lsplit[Ping, x |+| y](out)
        Cell.notifyEither[x, y](in, o1, o2).followUp()
        r.followUp()

      case _: -⚬.NotifyChoice[x, y] =>
        val (i1, i2, r) = Cell.rsplit[Pong, x |&| y](in)
        Cell.notifyChoice[x, y](i1, i2, out).followUp()
        r.followUp()
    }

  private def unify[A](l: Cell[A], r: Cell[A]): Unit =
    Cell.unify(l, r).followUp()

  extension (r: CellContent.ActionResult) {
    private def followUp(): Unit = {
      import CellContent.ActionResult._
      r match {
        case AllDone => // do nothing
        case UnificationRequest(x, y) => submitJob { () => unify(x, y) }
        case ConnectionRequest(x, f, y) => connectLater(x, f, y)
        case CallbackTriggered(f, x) => submitJob { () => f(x) }
        case Two(r1, r2) => r1.followUp(); r2.followUp()
        case i: Instruction => submitJob { () => i.execute().followUp() }
      }
    }
  }
}
