package libretto.scaletto.impl.concurrentcells

import libretto.scaletto.ScalettoExecution
import libretto.scaletto.impl.FreeScaletto
import libretto.util.Async
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

  override val InPort: ScalettoInPorts = ??? // TODO
  override val OutPort: ScalettoOutPorts = ??? // TODO

  def execute[A, B](prg: A -⚬ B): (InPort[A], OutPort[B]) = {
    val in = Cell.empty[A]
    val out = Cell.empty[B]
    submitJob { () => connect(in, prg, out) }
    (in, out)
  }

  def cancel(): Async[Unit] =
    ??? // TODO

  private def submitJob(action: Runnable): Unit =
    ec.execute(action)

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
          val (a1, a2) = Cell.split(in)
          val (b1, b2) = Cell.split(out)
          connectLater(a1, f1, b1)
          connectLater(a2, f2, b2)

        go[a1, a2, b1, b2](in, p.f, p.g, out)

      case -⚬.IntroFst() =>
        inline def go(out: Cell[One |*| A]): Unit =
          val (_, out1) = Cell.split(out)
          unify(in, out1)

        go(out)

      case -⚬.IntroSnd() =>
        inline def go(out: Cell[A |*| One]): Unit =
          val (out1, _) = Cell.split(out)
          unify(in, out1)

        go(out)

      case -⚬.ElimFst() =>
        inline def go(in: Cell[One |*| B]): Unit =
          val (_, in1) = Cell.split(in)
          unify(in1, out)

        go(in)

      case -⚬.ElimSnd() =>
        inline def go(in: Cell[B |*| One]): Unit =
          val (in1, _) = Cell.split(in)
          unify(in1, out)

        go(in)

      case _: -⚬.AssocLR[x, y, z] =>
        inline def go[X, Y, Z](in: Cell[(X |*| Y) |*| Z], out: Cell[X |*| (Y |*| Z)]): Unit =
          val (ixy, iz) = Cell.split(in)
          val (ix, iy)  = Cell.split(ixy)
          val (ox, oyz) = Cell.split(out)
          val (oy, oz)  = Cell.split(oyz)
          unify(ix, ox)
          unify(iy, oy)
          unify(iz, oz)

        go[x, y, z](in, out)

      case _: -⚬.AssocRL[x, y, z] =>
        inline def go[X, Y, Z](in: Cell[X |*| (Y |*| Z)], out: Cell[(X |*| Y) |*| Z]): Unit =
          val (ix, iyz) = Cell.split(in)
          val (iy, iz)  = Cell.split(iyz)
          val (oxy, oz) = Cell.split(out)
          val (ox, oy)  = Cell.split(oxy)
          unify(ix, ox)
          unify(iy, oy)
          unify(iz, oz)

        go[x, y, z](in, out)

      case _: -⚬.Swap[x, y] =>
        inline def go[X, Y](in: Cell[X |*| Y], out: Cell[Y |*| X]): Unit =
          val (ix, iy) = Cell.split(in)
          val (oy, ox) = Cell.split(out)
          unify(ix, ox)
          unify(iy, oy)

        go[x, y](in, out)

      case _: -⚬.InjectL[x, y] =>
        Cell.injectL[x, y](in, out).followUp()

      case _: -⚬.InjectR[x, y] =>
        Cell.injectR[x, y](in, out).followUp()

      case e: -⚬.EitherF[x, y, z] =>
        Cell.either[x, y, z](in, e.f, e.g, out).followUp()
    }

  private def unify[A](l: Cell[A], r: Cell[A]): Unit =
    Cell.unify(l, r).followUp()

  extension (r: Cell.ActionResult) {
    private def followUp(): Unit = {
      import Cell.ActionResult.{ConnectionRequest, Done}
      r match {
        case Done => // do nothing
        case ConnectionRequest(x, f, y) => connectLater(x, f, y)
      }
    }
  }
}
