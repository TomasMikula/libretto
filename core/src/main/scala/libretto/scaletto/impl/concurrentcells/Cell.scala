package libretto.scaletto.impl.concurrentcells

import java.util.concurrent.atomic.AtomicReference
import libretto.scaletto.impl.FreeScaletto._
import libretto.util.Async
import scala.annotation.tailrec

opaque type Cell[A] = AtomicReference[CellContent[A]]

object Cell {
  import CellContent.ActionResult

  def empty[A]: Cell[A] =
    new AtomicReference(CellContent.Empty())

  def split[A, B](cell: Cell[A |*| B]): (Cell[A], Cell[B]) =
    ??? // TODO

  def unify[A](l: Cell[A], r: Cell[A]): ActionResult =
    ??? // TODO

  def injectL[A, B](src: Cell[A], tgt: Cell[A |+| B]): ActionResult =
    ??? // TODO

  def injectR[A, B](src: Cell[B], tgt: Cell[A |+| B]): ActionResult =
    ??? // TODO

  def either[A, B, C](src: Cell[A |+| B], f: A -⚬ C, g: B -⚬ C, tgt: Cell[C]): ActionResult =
    ??? // TODO

  def supplyDone(tgt: Cell[Done]): ActionResult =
    tgt.modifyOpaque(CellContent.supplyDone)

  def awaitEither[A, B](src: Cell[A |+| B]): Async[Either[Throwable, Either[Cell[A], Cell[B]]]] =
    src.modifyOpaque(CellContent.awaitEither)

  extension [A](cell: Cell[A]) {
    def modifyOpaque[C](f: CellContent[A] => (CellContent[A], C)): C = {
      @tailrec def go(expected: CellContent[A]): C = {
        val res: (CellContent[A], C) = f(expected)
        val changed = compareAndSetOpaque(cell, expected, res._1)
        if (changed eq null)
          res._2
        else
          go(changed)
      }

      go(cell.getOpaque())
    }

    def modifyOpaqueWith[B, C](b: B, f: (CellContent[A], B) => (CellContent[A], C)): C = {
      @tailrec def go(expected: CellContent[A]): C = {
        val res: (CellContent[A], C) = f(expected, b)
        val changed = compareAndSetOpaque(cell, expected, res._1)
        if (changed eq null)
          res._2
        else
          go(changed)
      }

      go(cell.getOpaque())
    }
  }

  /** Returns `null` when successful, current value if different from expected. */
  @tailrec private def compareAndSetOpaque[A](
    cell: Cell[A],
    expected: CellContent[A],
    next: CellContent[A],
  ): CellContent[A] = {
    if (cell.weakCompareAndSetPlain(expected, next)) {
      null // success
    } else {
      val current = cell.getOpaque()
      if (current eq expected)
        compareAndSetOpaque(cell, expected, next)
      else
        current
    }
  }
}

sealed trait CellContent[A]
object CellContent {
  case class Empty[A]() extends CellContent[A]
  case object DoneSupplied extends CellContent[Done]
  case class EitherCallback[A, B](f: Either[Throwable, Either[Cell[A], Cell[B]]] => Unit) extends CellContent[A |+| B]

  enum ActionResult {
    case Done
    case ConnectionRequest[X, Y](l: Cell[X], f: X -⚬ Y, r: Cell[Y])
  }

  val supplyDone: CellContent[Done] => (CellContent[Done], ActionResult) = {
    case Empty()      => (DoneSupplied, ActionResult.Done)
    case DoneSupplied => throw new IllegalStateException("Double completion")
  }

  def awaitEither[A, B]: CellContent[A |+| B] => (CellContent[A |+| B], Async[Either[Throwable, Either[Cell[A], Cell[B]]]]) = {
    case Empty() =>
      val (completer, future) = Async.promiseLinear[Either[Throwable, Either[Cell[A], Cell[B]]]]
      (EitherCallback(completer), future)
    case EitherCallback(_) =>
      throw new IllegalStateException("Double observer")
  }
}
