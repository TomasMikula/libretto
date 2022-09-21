package libretto.scaletto.impl.concurrentcells

import java.util.concurrent.atomic.AtomicReference
import libretto.scaletto.impl.FreeScaletto._
import libretto.util.Async
import libretto.util.atomic._
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
