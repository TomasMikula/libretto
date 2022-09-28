package libretto.scaletto.impl.concurrentcells

import java.util.concurrent.atomic.AtomicReference
import libretto.scaletto.impl.FreeScaletto._
import libretto.util.Async
import libretto.util.atomic._
import scala.annotation.tailrec

opaque type Cell[A] <: AnyRef = AtomicReference[CellContent[A]]

object Cell {
  import CellContent.ActionResult

  def empty[A]: Cell[A] =
    new AtomicReference(CellContent.Empty())

  def lsplit[A, B](cell: Cell[A |*| B]): (Cell[A], Cell[B]) =
    cell.modifyOpaque(CellContent.lsplit)

  def rsplit[A, B](cell: Cell[A |*| B]): (Cell[A], Cell[B]) =
    cell.modifyOpaque(CellContent.rsplit)

  def unify[A](l: Cell[A], r: Cell[A]): ActionResult =
    r.modifyContentWith((l, r), CellContent.lFwd) match {
      case ActionResult.AllDone =>
        ActionResult.RForward(l, r)
      case r: ActionResult.RefineRFwd[_] =>
        r
      case r: ActionResult.ContractCell[_] =>
        r
    }

  def injectL[A, B](src: Cell[A], tgt: Cell[A |+| B]): ActionResult =
    tgt.modifyContentWith(src, CellContent.injectL)

  def injectR[A, B](src: Cell[B], tgt: Cell[A |+| B]): ActionResult =
    tgt.modifyContentWith(src, CellContent.injectR)

  def either[A, B, C](src: Cell[A |+| B], f: A -⚬ C, g: B -⚬ C, tgt: Cell[C]): ActionResult =
    ??? // TODO

  def chooseL[A, B](choiceCell: Cell[A |&| B], resultCell: Cell[A]): ActionResult =
    choiceCell.modifyContentWith((choiceCell, resultCell), CellContent.chooseL)

  def choice[A, B, C](tgt: Cell[A], f: A -⚬ B, g: A -⚬ C, src: Cell[B |&| C]): ActionResult =
    src.modifyContentWith(CellContent.ChooseFrom(tgt, f, g), CellContent.chooseFrom)

  def join(src1: Cell[Done], src2: Cell[Done], tgt: Cell[Done]): ActionResult =
    tgt.modifyContentWith((CellContent.JoinOf(src1, src2), tgt), CellContent.makeAJoinOf)

  def supplyDone(tgt: Cell[Done]): ActionResult =
    tgt.modifyOpaque(CellContent.supplyDone)

  def awaitDone(src: Cell[Done]): Async[Either[Throwable, Unit]] =
    src.modifyOpaque(CellContent.awaitDone)

  def awaitEither[A, B](
    src: Cell[A |+| B],
    listener: Either[Throwable, Either[Cell[A], Cell[B]]] => Unit,
  ): ActionResult =
    src.modifyContentWith((src, listener), CellContent.awaitEither)

  extension [A](cell: Cell[A]) {
    def modifyContent[R](f: CellContent[A] => (CellContent[A], R)): R =
      cell.modifyOpaque(f)

    def modifyContentWith[B, R](b: B, f: (CellContent[A], B) => (CellContent[A], R)): R =
      cell.modifyOpaqueWith(b, f)
  }
}

sealed trait CellContent[A]
object CellContent {
  case class Empty[A]() extends CellContent[A]
  sealed trait LDefined[A] extends CellContent[A]
  sealed trait RDefined[A] extends CellContent[A]
  case class BiDef[A](l: LDefined[A], r: RDefined[A]) extends CellContent[A]
  case class Consumed[A]() extends CellContent[A]

  sealed trait LComplete[A] extends LDefined[A]
  // sealed trait LIncomplete[A] extends LDefined[A]

  sealed trait RComplete[A] extends RDefined[A]
  // sealed trait RIncomplete[A] extends RDefined[A]

  case class LFwd[A](tgt: Cell[A]) extends LDefined[A]
  case class RFwd[A](tgt: Cell[A]) extends RDefined[A]

  // case class LLink[A, B](tgt: Cell[A], link: Link[A, B]) extends LDefined[B]
  case class RLink[A, B](link: Relation[A, B], tgt: Cell[B]) extends RDefined[A]

  case object DoneSupplied extends LComplete[Done]
  case class DoneCallback(f: Either[Throwable, Unit] => Unit) extends RDefined[Done]

  case class LSplit[A1, A2](cell1: Cell[A1], cell2: Cell[A2]) extends LDefined[A1 |*| A2]
  case class RSplit[A1, A2](cell1: Cell[A1], cell2: Cell[A2]) extends RDefined[A1 |*| A2]

  case class InjectedL[A, B](value: Cell[A]) extends LDefined[A |+| B]
  case class InjectedR[A, B](value: Cell[B]) extends LDefined[A |+| B]
  case class EitherCallback[A, B](f: Either[Throwable, Either[Cell[A], Cell[B]]] => Unit) extends RDefined[A |+| B]

  case class ChosenL[A, B](resultCell: Cell[A]) extends RDefined[A |&| B]
  case class ChosenR[A, B](resultCell: Cell[B]) extends RDefined[A |&| B]
  case class ChooseFrom[A, B, C](tgt: Cell[A], f: A -⚬ B, g: A -⚬ C) extends LDefined[B |&| C]

  case class JoinOf(src1: Cell[Done], src2: Cell[Done]) extends LDefined[Done]

  // /** Result type that means that a link has been recorded. */
  // case object Linked

  // sealed trait Link[A, B]
  // object Link {
  // }

  sealed trait ActionResult
  object ActionResult {
    case object AllDone extends ActionResult

    sealed trait FollowUpAction extends ActionResult {
      def and(that: FollowUpAction): FollowUpAction =
        Two(this, that)
    }

    case class Two(_1: FollowUpAction, _2: FollowUpAction) extends FollowUpAction

    case class ConnectionRequest[X, Y](l: Cell[X], f: X -⚬ Y, r: Cell[Y]) extends FollowUpAction

    case class CallbackTriggered[X](f: X => Unit, x: X) extends FollowUpAction

    sealed trait Instruction extends FollowUpAction {
      def execute(): ActionResult
    }

    /** An action to refine `src` by pointing it at `receiver`.
      *
      * @param src must be yet unconnected to the right
      * @param rel
      * @param receiver must already know that it will be fed from `src`
      */
    case class DirectTo[A, B](src: Cell[A], rel: Relation[A, B], receiver: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        src.modifyContentWith(RLink(rel, receiver), CellContent.directTo)
    }

    case class RefineLFwd[A](cell: Cell[A], expectedLTarget: Cell[A], payload: LDefined[A]) extends Instruction {
      override def execute(): ActionResult =
        cell.modifyContentWith(this, CellContent.refineLFwd)
    }

    case class RefineRFwd[A](cell: Cell[A], expectedRTarget: Cell[A], payload: RDefined[A]) extends Instruction {
      override def execute(): ActionResult =
        ???
    }

    case class RForward[A](src: Cell[A], tgt: Cell[A]) extends Instruction {
      override def execute(): ActionResult =
        src.modifyContentWith((src, tgt), CellContent.rFwd)
    }

    sealed trait ContractCell[A] extends Instruction {
      override def execute(): ActionResult = ???
    }
    case class ContractBiFwd[A](l: Cell[A], slated: Cell[A], r: Cell[A]) extends ContractCell[A]
    case class ContractLFwd[A, B](l: Cell[A], slated: Cell[A], rRel: Relation[A, B], r: Cell[B]) extends ContractCell[A]
    case class ContractRFwd[A, B](l: Cell[A], lRel: Relation[A, B], slated: Cell[B], r: Cell[B]) extends ContractCell[B]
  }
  import ActionResult._

  val supplyDone: CellContent[Done] => (CellContent[Done], ActionResult) = {
    case Empty()      => (DoneSupplied, ActionResult.AllDone)
    case DoneSupplied => throw new IllegalStateException("Double completion")
  }

  def lsplit[A, B]: CellContent[A |*| B] => (CellContent[A |*| B], (Cell[A], Cell[B])) = {
    case Empty() =>
      val a = Cell.empty[A]
      val b = Cell.empty[B]
      (LSplit(a, b), (a, b))
    case RSplit(a, b) =>
      (Consumed(), (a, b))
    case _: LDefined[A |*| B] | Consumed() =>
      throw new IllegalStateException("The cell is already left-connected")
  }

  def rsplit[A, B]: CellContent[A |*| B] => (CellContent[A |*| B], (Cell[A], Cell[B])) = {
    case Empty() =>
      val a = Cell.empty[A]
      val b = Cell.empty[B]
      (RSplit(a, b), (a, b))
    case LSplit(a, b) =>
      (Consumed(), (a, b))
    case _: RDefined[A |*| B] | Consumed() =>
      throw new IllegalStateException("The cell is already right-connected")
  }

  def injectL[A, B]: (CellContent[A |+| B], Cell[A]) => (CellContent[A |+| B], ActionResult) = {
    (tgt, src) =>
      tgt match {
        case Empty() =>
          (InjectedL(src), ActionResult.AllDone)
        case EitherCallback(f) =>
          (Consumed(), ActionResult.CallbackTriggered(f, Right(Left(src))))
        case _: LDefined[A |+| B] | Consumed() =>
          throw new IllegalStateException("The target cell is already left-connected")
      }
  }

  def injectR[A, B]: (CellContent[A |+| B], Cell[B]) => (CellContent[A |+| B], ActionResult) = {
    (tgt, src) =>
      tgt match {
        case Empty() =>
          (InjectedR(src), ActionResult.AllDone)
        case EitherCallback(f) =>
          (Consumed(), ActionResult.CallbackTriggered(f, Right(Right(src))))
        case _: LDefined[A |+| B] | Consumed() =>
          throw new IllegalStateException("The target cell is already left-connected")
      }
  }

  def chooseL[A, B]: (CellContent[A |&| B], (Cell[A |&| B], Cell[A])) => (CellContent[A |&| B], ActionResult) = {
    (choiceContent, cells) =>
      val (choiceCell, resultCell) = cells
      choiceContent match {
        case Empty() =>
          (ChosenL(resultCell), ActionResult.AllDone)
        case LFwd(tgt) =>
          (Consumed(), RefineRFwd(tgt, expectedRTarget = choiceCell, ChosenL(resultCell)))
      }
  }

  def chooseFrom[A, B, C]: (CellContent[B |&| C], ChooseFrom[A, B, C]) => (CellContent[B |&| C], ActionResult) = {
    (src, ch) =>
      src match {
        case Empty() => (ch, ActionResult.AllDone)
      }
  }

  val makeAJoinOf: (CellContent[Done], (JoinOf, Cell[Done])) => (CellContent[Done], ActionResult) = {
    (tgt, joinersTgtCell) =>
      import ActionResult.DirectTo
      import Relation.{JoinerFst, JoinerSnd}

      val (joiners, tgtCell) = joinersTgtCell
      tgt match {
        case Empty() =>
          val followUp =
            DirectTo(joiners.src1, JoinerFst, tgtCell)
              .and(DirectTo(joiners.src2, JoinerSnd, tgtCell))
          (joiners, followUp)
        case r: RDefined[Done] =>
          val followUp =
            DirectTo(joiners.src1, JoinerFst, tgtCell)
              .and(DirectTo(joiners.src2, JoinerSnd, tgtCell))
          (BiDef(joiners, r), followUp)
      }
  }

  def directTo[A, B]: (CellContent[A], RLink[A, B]) => (CellContent[A], ActionResult) = {
    (src, rLink) =>
      src match {
        case Empty()   => (rLink, ActionResult.AllDone)
        case l: JoinOf => (BiDef(l, rLink), ActionResult.AllDone)
      }
  }

  def lFwd[A]: (CellContent[A], (Cell[A], Cell[A])) => (CellContent[A], AllDone.type | ContractCell[A] | RefineRFwd[A]) = {
    (rContent, cells) =>
      val (lCell, rCell) = cells
      rContent match {
        case Empty() => (LFwd(lCell), AllDone)
        case c: ChosenL[a1, a2] => (Consumed(), RefineRFwd[a1 |&| a2](lCell, expectedRTarget = rCell, c))
      }
  }

  def rFwd[A]: (CellContent[A], (Cell[A], Cell[A])) => (CellContent[A], AllDone.type | ContractCell[A] | RefineLFwd[A]) = {
    (lContent, cells) =>
      val (lCell, rCell) = cells
      lContent match {
        case Empty() => (RFwd(rCell), AllDone)
        case DoneSupplied => (Consumed(), RefineLFwd(rCell, expectedLTarget = lCell, DoneSupplied))
        case l: LFwd[x] => (BiDef(l, RFwd(rCell)), ContractBiFwd(l.tgt, slated = lCell, rCell))
        case c: ChooseFrom[x, y, z] => (BiDef(c, RFwd(rCell)), AllDone)
      }
  }

  def refineLFwd[A]: (CellContent[A], RefineLFwd[A]) => (CellContent[A], ActionResult) = {
    (rContent, refinement) =>
      val RefineLFwd(_, expectedLCell, payload) = refinement
      rContent match {
        case LFwd(tgt) =>
          if (tgt eq expectedLCell) {
            (payload, AllDone)
          } else {
            throw new IllegalStateException(s"Actual LFwd target did not equal expected: $tgt vs. $expectedLCell")
          }
        case Empty() =>
          (payload, AllDone)
      }
  }

  val awaitDone: CellContent[Done] => (CellContent[Done], Async[Either[Throwable, Unit]]) = {
    case Empty() =>
      val (completer, async) = Async.promiseLinear[Either[Throwable, Unit]]
      (DoneCallback(completer), async)
    case j: JoinOf =>
      val (completer, async) = Async.promiseLinear[Either[Throwable, Unit]]
      (BiDef(j, DoneCallback(completer)), async)
  }

  def awaitEither[A, B](
    eitherContent: CellContent[A |+| B],
    cellAndListener: (Cell[A |+| B], Either[Throwable, Either[Cell[A], Cell[B]]] => Unit),
  ): (CellContent[A |+| B], ActionResult) = {
    val (eitherCell, listener) = cellAndListener
    eitherContent match {
      case Empty() =>
        (EitherCallback(listener), AllDone)
      case InjectedL(cell) =>
        (Consumed(), CallbackTriggered(listener, Right(Left(cell))))
      case InjectedR(cell) =>
        (Consumed(), CallbackTriggered(listener, Right(Right(cell))))
      case LFwd(tgt) =>
        (Consumed(), RefineRFwd(tgt, expectedRTarget = eitherCell, EitherCallback(listener)))
      case EitherCallback(_) | Consumed() =>
        throw new IllegalStateException("Double observer")
    }
  }
}

enum Relation[A, B] {
  case JoinerFst extends Relation[Done, Done]
  case JoinerSnd extends Relation[Done, Done]
}
