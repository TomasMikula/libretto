package libretto.scaletto.impl.concurrentcells

import java.util.concurrent.atomic.AtomicReference
import libretto.scaletto.impl.FreeScaletto._

opaque type Cell[A] = AtomicReference[CellContent[A]]

object Cell {
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

  enum ActionResult {
    case Done
    case ConnectionRequest[X, Y](l: Cell[X], f: X -⚬ Y, r: Cell[Y])
  }
}

sealed trait CellContent[A]
object CellContent {
  case class Empty[A]() extends CellContent[A]
}
