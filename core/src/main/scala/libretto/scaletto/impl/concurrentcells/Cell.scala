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

  def lsplit[A, B](cell: Cell[A |*| B]): (Cell[A], Cell[B], ActionResult) =
    cell.modifyContentWith(cell, CellContent.lsplit)

  def rsplit[A, B](cell: Cell[A |*| B]): (Cell[A], Cell[B], ActionResult) =
    cell.modifyContentWith(cell, CellContent.rsplit)

  def unify[A](l: Cell[A], r: Cell[A]): ActionResult =
    r.modifyContentWith((l, r), CellContent.lFwd) match {
      case ActionResult.AllDone =>
        ActionResult.RReciprocateForward(l, r)
      case r: ActionResult.RefineRFwd[_] =>
        r
      case r: ActionResult.ContractCell[_] =>
        r
    }

  def injectL[A, B](src: Cell[A], tgt: Cell[A |+| B]): ActionResult =
    tgt.modifyContentWith(src, CellContent.injectL)

  def injectR[A, B](src: Cell[B], tgt: Cell[A |+| B]): ActionResult =
    tgt.modifyContentWith((src, tgt), CellContent.injectR)

  def either[A, B, C](src: Cell[A |+| B], f: A -⚬ C, g: B -⚬ C, tgt: Cell[C]): ActionResult =
    src.modifyContentWith(CellContent.EitherSwitch(f, g, tgt), CellContent.eitherSwitch)

  def chooseL[A, B](choiceCell: Cell[A |&| B], resultCell: Cell[A]): ActionResult =
    choiceCell.modifyContentWith((choiceCell, resultCell), CellContent.chooseL)

  def chooseR[A, B](choiceCell: Cell[A |&| B], resultCell: Cell[B]): ActionResult =
    choiceCell.modifyContentWith((choiceCell, resultCell), CellContent.chooseR)

  def choice[A, B, C](tgt: Cell[A], f: A -⚬ B, g: A -⚬ C, src: Cell[B |&| C]): ActionResult =
    src.modifyContentWith(CellContent.ChooseFrom(tgt, f, g), CellContent.chooseFrom)

  def choiceWith[A, B, C](tgt: Cell[(A |*| B) |&| (A |*| C)], addendum: Cell[A], src: Cell[B |&| C]): ActionResult =
    src.modifyContentWith(CellContent.ChoiceWith(tgt, addendum), CellContent.choiceWith)

  def join(src1: Cell[Done], src2: Cell[Done], tgt: Cell[Done]): ActionResult =
    tgt.modifyContentWith((tgt, CellContent.JoinOf(src1, src2)), CellContent.makeAJoinOf)

  def supplyDone(tgt: Cell[Done]): ActionResult =
    tgt.modifyContentWith(tgt, CellContent.supplyDone)

  def select(choiceCell: Cell[One |&| One], contestant1: Cell[Pong], contestant2: Cell[Pong]): ActionResult =
    choiceCell.modifyContentWith(
      (choiceCell, CellContent.SelectOf(contestant1, contestant2)),
      CellContent.makeASelectOf,
    )

  def awaitDone(
    src: Cell[Done],
    listener: Either[Throwable, Unit] => Unit,
  ): ActionResult =
    src.modifyContentWith((src, listener), CellContent.awaitDone)

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

    def modifyContentOptWith[B, R](b: B, f: (CellContent[A], B) => (Option[CellContent[A]], R)) : R =
      cell.modifyOpaqueOptWith(b, f)
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

  sealed trait RComplete[A] extends RDefined[A]

  case class LFwd[A](tgt: Cell[A]) extends LDefined[A]
  case class RFwd[A](tgt: Cell[A]) extends RDefined[A]

  case class LBypassing[A](newTgt: Cell[A], oldTgt: Cell[A]) extends LDefined[A]

  // case class LLink[A, B](tgt: Cell[A], link: Link[A, B]) extends LDefined[B]
  case class RLink[A, B](link: RoleR[A, B], tgt: Cell[B]) extends RDefined[A]

  case object DoneSupplied extends LComplete[Done]
  case class DoneCallback(f: Either[Throwable, Unit] => Unit) extends RComplete[Done]

  case class LSplit[A1, A2](cell1: Cell[A1], cell2: Cell[A2]) extends LComplete[A1 |*| A2]
  case class RSplit[A1, A2](cell1: Cell[A1], cell2: Cell[A2]) extends RComplete[A1 |*| A2]

  case class InjectedL[A, B](value: Cell[A]) extends LComplete[A |+| B]
  case class InjectedR[A, B](value: Cell[B]) extends LComplete[A |+| B]
  case class EitherSwitch[A, B, C](f: A -⚬ C, g: B -⚬ C, tgt: Cell[C]) extends LDefined[A |+| B]
  case class EitherCallback[A, B](f: Either[Throwable, Either[Cell[A], Cell[B]]] => Unit) extends RComplete[A |+| B]

  case class ChosenL[A, B](resultCell: Cell[A]) extends RComplete[A |&| B]
  case class ChosenR[A, B](resultCell: Cell[B]) extends RComplete[A |&| B]
  case class ChooseFrom[A, B, C](tgt: Cell[A], f: A -⚬ B, g: A -⚬ C) extends LDefined[B |&| C]
  case class ChoiceWith[A, B, C](tgt: Cell[(A |*| B) |&| (A |*| C)], addendum: Cell[A]) extends LDefined[B |&| C]

  case class JoinOf(src1: Cell[Done], src2: Cell[Done]) extends LDefined[Done]

  case class SelectOf(contestant1: Cell[Pong], contestant2: Cell[Pong]) extends RDefined[One |&| One]

  sealed trait ActionResult
  object ActionResult {
    case object AllDone extends ActionResult

    sealed trait FollowUpAction extends ActionResult {
      def and(that: FollowUpAction): FollowUpAction =
        Two(this, that)
    }

    case class Two(_1: FollowUpAction, _2: FollowUpAction) extends FollowUpAction

    case class UnificationRequest[X](l: Cell[X], r: Cell[X]) extends FollowUpAction
    case class ConnectionRequest[X, Y](l: Cell[X], f: X -⚬ Y, r: Cell[Y]) extends FollowUpAction

    case class CallbackTriggered[X](f: X => Unit, x: X) extends FollowUpAction

    sealed trait Instruction extends FollowUpAction {
      def execute(): ActionResult
    }

    /** An action to refine `src` by pointing it at `receiver` to its right.
      *
      * @param src must be yet unconnected to the right
      * @param rel the role `src` plays in `receiver`
      * @param receiver must already know that it will be fed from `src`
      */
    case class DirectToR[A, B](src: Cell[A], rel: RoleR[A, B], receiver: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        src.modifyContentWith(RLink(rel, receiver), CellContent.directTo)
    }

    /** An action to refine `src` by pointing it at `receiver` to its left.
      *
      * @param src must be yet unconnected to the right
      * @param rel the role `src` plays in `receiver`
      * @param receiver must already know that it will be fed from `src`
      */
    case class DirectToL[A, B](receiver: Cell[A], rel: RoleL[A, B], src: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        ???
    }

    case class RefineLFwd[A](cell: Cell[A], expectedLTarget: Cell[A], payload: LComplete[A]) extends Instruction {
      override def execute(): ActionResult =
        cell.modifyContentWith(this, CellContent.refineLFwd)
    }

    case class RefineRFwd[A](cell: Cell[A], expectedRTarget: Cell[A], payload: RComplete[A]) extends Instruction {
      override def execute(): ActionResult =
        cell.modifyContentWith(this, CellContent.refineRFwd)
    }

    case class RReciprocateForward[A](src: Cell[A], tgt: Cell[A]) extends Instruction {
      override def execute(): ActionResult =
        src.modifyContentOptWith((src, tgt), CellContent.rReciprocateFwd)
    }

    sealed trait ContractCell[A] extends Instruction

    case class ContractBiFwd[A](l: Cell[A], slated: Cell[A], r: Cell[A]) extends ContractCell[A] {
      override def execute(): ActionResult =
        r.modifyContentOptWith((l, slated, r), CellContent.initLBypass)
    }

    case class ContractLFwd[A, B](l: Cell[A], slated: Cell[A], rRel: RoleR[A, B], r: Cell[B]) extends ContractCell[A] {
      override def execute(): ActionResult = ???
    }

    case class ContractRFwd[A, B](l: Cell[A], lRel: RoleL[A, B], slated: Cell[B], r: Cell[B]) extends ContractCell[B] {
      override def execute(): ActionResult = ???
    }

    case class SkipAhead[A](l: Cell[A], m: Cell[A], r: Cell[A]) extends Instruction {
      override def execute(): ActionResult =
        l.modifyContentOptWith(this, CellContent.skipAhead)
    }

    case class CompleteLBypass[A](l: Cell[A], bypassed: Cell[A], r: Cell[A]) extends Instruction {
      override def execute(): ActionResult =
        r.modifyContentOptWith(this, CellContent.completeLBypass)
    }

    case class ConsumeBypassedCell[A](l: Cell[A], bypassed: Cell[A], r: Cell[A]) extends Instruction {
      override def execute(): ActionResult =
        bypassed.modifyContentOptWith(this, CellContent.consumeBypassedCell)
    }
  }
  import ActionResult._

  val supplyDone: (CellContent[Done], Cell[Done]) => (CellContent[Done], ActionResult) = {
    (content, cell) =>
      content match
        case Empty()      => (DoneSupplied, ActionResult.AllDone)
        case DoneSupplied => throw new IllegalStateException("Double completion")
        case RFwd(tgt)    => (Consumed(), RefineLFwd(tgt, expectedLTarget = cell, DoneSupplied))
  }

  def lsplit[A, B]: (CellContent[A |*| B], Cell[A |*| B]) => (CellContent[A |*| B], (Cell[A], Cell[B], ActionResult)) = {
    (content, self) =>
      content match
        case Empty() =>
          val a = Cell.empty[A]
          val b = Cell.empty[B]
          (LSplit(a, b), (a, b, AllDone))
        case RSplit(a, b) =>
          (Consumed(), (a, b, AllDone))
        case RFwd(tgt) =>
          val a = Cell.empty[A]
          val b = Cell.empty[B]
          (Consumed(), (a, b, RefineLFwd(tgt, expectedLTarget = self, LSplit(a, b))))
        case _: LDefined[A |*| B] | Consumed() =>
          throw new IllegalStateException("The cell is already left-connected")
  }

  def rsplit[A, B]: (CellContent[A |*| B], Cell[A |*| B]) => (CellContent[A |*| B], (Cell[A], Cell[B], ActionResult)) = {
    (content, self) =>
      content match
        case Empty() =>
          val a = Cell.empty[A]
          val b = Cell.empty[B]
          (RSplit(a, b), (a, b, AllDone))
        case LSplit(a, b) =>
          (Consumed(), (a, b, AllDone))
        case LFwd(tgt) =>
          val a = Cell.empty[A]
          val b = Cell.empty[B]
          (Consumed(), (a, b, RefineRFwd(tgt, expectedRTarget = self, RSplit(a, b))))
        case bp @ LBypassing(_, _) =>
          val a = Cell.empty[A]
          val b = Cell.empty[B]
          (BiDef(bp, RSplit(a, b)), (a, b, AllDone))
        case _: RDefined[A |*| B] | Consumed() =>
          throw new IllegalStateException("The cell is already right-connected")
  }

  def injectL[A, B]: (CellContent[A |+| B], Cell[A]) => (CellContent[A |+| B], ActionResult) = {
    (tgt, src) =>
      tgt match {
        case Empty() =>
          (InjectedL(src), AllDone)
        case EitherCallback(f) =>
          (Consumed(), CallbackTriggered(f, Right(Left(src))))
        case _: LDefined[A |+| B] | Consumed() =>
          throw new IllegalStateException("The target cell is already left-connected")
      }
  }

  def injectR[A, B]: (CellContent[A |+| B], (Cell[B], Cell[A |+| B])) => (CellContent[A |+| B], ActionResult) = {
    (tgtContent, cells) =>
      val (srcCell, tgtCell) = cells
      tgtContent match {
        case Empty() =>
          (InjectedR(srcCell), AllDone)
        case EitherCallback(f) =>
          (Consumed(), CallbackTriggered(f, Right(Right(srcCell))))
        case RFwd(tgt1) =>
          (Consumed(), RefineLFwd(tgt1, expectedLTarget = tgtCell, InjectedR(srcCell)))
        case _: LDefined[A |+| B] | Consumed() =>
          throw new IllegalStateException("The target cell is already left-connected")
      }
  }

  def eitherSwitch[A, B, C]: (CellContent[A |+| B], EitherSwitch[A, B, C]) => (CellContent[A |+| B], ActionResult) = {
    (eitherContent, es) =>
      eitherContent match {
        case Empty() => (es, AllDone)
      }
  }

  def chooseL[A, B]: (CellContent[A |&| B], (Cell[A |&| B], Cell[A])) => (CellContent[A |&| B], ActionResult) = {
    (choiceContent, cells) =>
      val (choiceCell, resultCell) = cells
      choiceContent match {
        case Empty() =>
          (ChosenL(resultCell), AllDone)
        case LFwd(tgt) =>
          (Consumed(), RefineRFwd(tgt, expectedRTarget = choiceCell, ChosenL(resultCell)))
      }
  }

  def chooseR[A, B]: (CellContent[A |&| B], (Cell[A |&| B], Cell[B])) => (CellContent[A |&| B], ActionResult) = {
    (choiceContent, cells) =>
      val (choiceCell, resultCell) = cells
      choiceContent match {
        case Empty() =>
          (ChosenR(resultCell), AllDone)
        case LFwd(tgt) =>
          (Consumed(), RefineRFwd(tgt, expectedRTarget = choiceCell, ChosenR(resultCell)))
      }
  }

  def chooseFrom[A, B, C]: (CellContent[B |&| C], ChooseFrom[A, B, C]) => (CellContent[B |&| C], ActionResult) = {
    (src, ch) =>
      src match {
        case Empty() => (ch, AllDone)
        case rFwd @ RFwd(_) => (BiDef(ch, rFwd), AllDone)
      }
  }

  def choiceWith[A, B, C]: (CellContent[B |&| C], ChoiceWith[A, B, C]) => (CellContent[B |&| C], ActionResult) = {
    (src, ch) =>
      src match {
        case Empty() => (ch, AllDone)
      }
  }

  val makeAJoinOf: (CellContent[Done], (Cell[Done], JoinOf)) => (CellContent[Done], ActionResult) = {
    (content, cellAndJoiners) =>
      import RoleR.{Joiner1, Joiner2}

      val (self, joiners) = cellAndJoiners
      content match {
        case Empty() =>
          val followUp =
            DirectToR(joiners.src1, Joiner1, self) and
            DirectToR(joiners.src2, Joiner2, self)
          (joiners, followUp)
        case r: RDefined[Done] =>
          val followUp =
            DirectToR(joiners.src1, Joiner1, self) and
            DirectToR(joiners.src2, Joiner2, self)
          (BiDef(joiners, r), followUp)
      }
  }

  val makeASelectOf: (CellContent[One |&| One], (Cell[One |&| One], SelectOf)) => (CellContent[One |&| One], ActionResult) = {
    (content, cellAndContestants) =>
      import RoleL.{SelectContestant1, SelectContestant2}

      val (self, contestants) = cellAndContestants
      content match {
        case Empty() =>
          val followUp =
            DirectToL(self, SelectContestant1, contestants.contestant1) and
            DirectToL(self, SelectContestant2, contestants.contestant2)
          (contestants, followUp)
        case l @ LFwd(_) =>
          val followUp =
            DirectToL(self, SelectContestant1, contestants.contestant1) and
            DirectToL(self, SelectContestant2, contestants.contestant2)
          (BiDef(l, contestants), followUp)
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
        case Empty()                 => (LFwd(lCell), AllDone)
        case c: ChosenL[a1, a2]      => (Consumed(), RefineRFwd[a1 |&| a2](lCell, expectedRTarget = rCell, c))
        case e: EitherCallback[x, y] => (Consumed(), RefineRFwd[x |+| y](lCell, expectedRTarget = rCell, e))
        case r: RSplit[x, y]         => (Consumed(), RefineRFwd[x |*| y](lCell, expectedRTarget = rCell, r))
        case cb: DoneCallback        => (Consumed(), RefineRFwd[Done](lCell, expectedRTarget = rCell, cb))
        case rFwd: RFwd[a]           => (BiDef(LFwd(lCell), rFwd), ContractBiFwd(lCell, rCell, rFwd.tgt))
        case rLnk @ RLink(rel, tgt)  => (BiDef(LFwd(lCell), rLnk), ContractLFwd(lCell, rCell, rel, tgt))
      }
  }

  def rReciprocateFwd[A]: (CellContent[A], (Cell[A], Cell[A])) => (Option[CellContent[A]], AllDone.type | ContractCell[A] | RefineLFwd[A]) = {
    (lContent, cells) =>
      val (self, rCell) = cells
      lContent match {
        case Empty()                => (Some(RFwd(rCell)), AllDone)
        case DoneSupplied           => (Some(Consumed()), RefineLFwd(rCell, expectedLTarget = self, DoneSupplied))
        case l: LSplit[x, y]        => (Some(Consumed()), RefineLFwd(rCell, expectedLTarget = self, l))
        case i: InjectedR[x, y]     => (Some(Consumed()), RefineLFwd(rCell, expectedLTarget = self, i))
        case l: LFwd[x]             => (Some(BiDef(l, RFwd(rCell))), ContractBiFwd(l.tgt, slated = self, rCell))
        case j: JoinOf              => (Some(BiDef(j, RFwd(rCell))), AllDone)
        case c: ChooseFrom[x, y, z] => (Some(BiDef(c, RFwd(rCell))), AllDone)
        case c: ChoiceWith[x, y, z] => (Some(BiDef(c, RFwd(rCell))), AllDone)
        case l: LBypassing[x]       => (Some(BiDef(l, RFwd(rCell))), AllDone)

        // overtaken
        case RSplit(_, _) => (None, AllDone)
        case ChosenR(_)   => (None, AllDone)
        case ChosenL(_)   => (None, AllDone)
        case Consumed()   => (None, AllDone)
      }
  }

  def refineLFwd[A]: (CellContent[A], RefineLFwd[A]) => (CellContent[A], ActionResult) = {
    (rContent, refinement) =>
      val RefineLFwd(self, expectedLCell, payload) = refinement
      rContent match {
        case LFwd(tgt) =>
          if (tgt eq expectedLCell) {
            (payload, AllDone)
          } else {
            throw new IllegalStateException(s"Actual LFwd target did not equal expected: $tgt vs. $expectedLCell")
          }
        case LBypassing(newTgt, oldTgt) =>
          if ((newTgt eq expectedLCell) || (oldTgt eq expectedLCell))
            (payload, AllDone)
          else
            throw new IllegalStateException(s"Neither old ($oldTgt) nor new ($newTgt) target of LBypassing equals the expected target $expectedLCell")
        case BiDef(l, r) =>
          val l1 = l match {
            case LFwd(tgt) =>
              if (tgt eq expectedLCell) {
                payload
              } else {
                throw new IllegalStateException(s"Actual LFwd target did not equal expected: $tgt vs. $expectedLCell")
              }
          }
          combineLCompleteRDefined(self, l1, r)
        case Empty() =>
          (payload, AllDone)
        case Consumed() =>
          (Consumed(), AllDone)
      }
  }

  def refineRFwd[A]: (CellContent[A], RefineRFwd[A]) => (CellContent[A], ActionResult) = {
    (lContent, refinement) =>
      val RefineRFwd(self, expectedRCell, payload) = refinement
      lContent match {
        case RFwd(tgt) =>
          if (tgt eq expectedRCell) {
            (payload, AllDone)
          } else {
            throw new IllegalStateException(s"Actual RFwd target did not equal expected: $tgt vs. $expectedRCell")
          }
        case BiDef(l, r) =>
          val r1 = r match {
            case RFwd(tgt) =>
              if (tgt eq expectedRCell) {
                payload
              } else {
                throw new IllegalStateException(s"Actual RFwd target did not equal expected: $tgt vs. $expectedRCell")
              }
          }
          combineLDefinedRComplete(self, l, r1)
        case l: LDefined[A] =>
          combineLDefinedRComplete(self, l, payload)
        case Empty() =>
          (payload, AllDone)
        case Consumed() =>
          (Consumed(), AllDone)
      }
  }

  private def combineLDefinedRComplete[A](self: Cell[A], l: LDefined[A], r: RComplete[A]): (CellContent[A], ActionResult) =
    r match
      case cb @ DoneCallback(listener) =>
        l match
          case DoneSupplied => (Consumed(), CallbackTriggered(listener, Right(())))
          case j: JoinOf    => (BiDef(j, cb), AllDone)
      case cb @ EitherCallback(listener) =>
        l match
          case InjectedL(cell) => (Consumed(), CallbackTriggered(listener, Right(Left(cell))))
          case InjectedR(cell) => (Consumed(), CallbackTriggered(listener, Right(Right(cell))))
      case r @ RSplit(b1, b2) =>
        l match
          case LSplit(a1, a2) => (Consumed(), UnificationRequest(a1, b1) and UnificationRequest(a2, b2))
          case LFwd(lTgt)     => (Consumed(), RefineRFwd(lTgt, expectedRTarget = self, r))
      case cr @ ChosenR(resultCell) =>
        l match
          case LFwd(lTgt) => (Consumed(), RefineRFwd(lTgt, expectedRTarget = self, cr))
      case cl @ ChosenL(resultCell) =>
        l match
          case LFwd(lTgt)            => (Consumed(), RefineRFwd(lTgt, expectedRTarget = self, cl))
          case LBypassing(newTgt, _) => (Consumed(), RefineRFwd(newTgt, expectedRTarget = self, cl))

  private def combineLCompleteRDefined[A](self: Cell[A], l: LComplete[A], r: RDefined[A]): (CellContent[A], ActionResult) =
    l match
      case DoneSupplied =>
        r match
          case RFwd(tgt) => (Consumed(), RefineLFwd(tgt, expectedLTarget = self, DoneSupplied))

  private def combine[A](self: Cell[A], l: LDefined[A], r: RDefined[A]): (CellContent[A], ActionResult) =
    (l, r) match {
      case (lc: LComplete[A], r) => combineLCompleteRDefined(self, lc, r)
      case (l, rc: RComplete[A]) => combineLDefinedRComplete(self, l, rc)
    }

  def initLBypass[A]: (CellContent[A], (Cell[A], Cell[A], Cell[A])) => (Option[CellContent[A]], ActionResult) = {
    (rContent, cells) =>
      val (lCell, mCell, rCell) = cells
      rContent match {
        case Empty() =>
          (Some(LBypassing(lCell, mCell)), SkipAhead(lCell, mCell, rCell))
        case LFwd(tgt) =>
          if (tgt eq mCell)
            (Some(LBypassing(lCell, mCell)), SkipAhead(lCell, mCell, rCell))
          else // overtaken
            (None, AllDone)
        case BiDef(l, r) =>
          r match
            case RFwd(_) => // obstructed by higher-priority task (rCell is being bypassed)
              (None, AllDone)
        case Consumed() =>
          (None, AllDone)
      }
  }

  def skipAhead[A]: (CellContent[A], SkipAhead[A]) => (Option[CellContent[A]], ActionResult) = {
    (lContent, cells) =>
      val SkipAhead(lCell, mCell, rCell) = cells
      lContent match {
        case RFwd(tgt) =>
          if (tgt eq mCell)
            (Some(RFwd(rCell)), CompleteLBypass(lCell, mCell, rCell) and ConsumeBypassedCell(lCell, mCell, rCell))
          else // overtaken
            (None, AllDone)
        case BiDef(ll, lr) =>
          lr match {
            case RFwd(tgt) =>
              if (tgt eq mCell)
                (Some(BiDef(ll, RFwd(rCell))), CompleteLBypass(lCell, mCell, rCell) and ConsumeBypassedCell(lCell, mCell, rCell))
              else // overtaken
                (None, AllDone)
          }
        case Consumed() => // overtaken
          (None, AllDone)
        case DoneSupplied =>
          (
            Some(Consumed()),
            RefineLFwd(rCell, expectedLTarget = lCell, DoneSupplied) and
              ConsumeBypassedCell(lCell, mCell, rCell)
          )
        case Empty() =>
          (Some(RFwd(rCell)), CompleteLBypass(lCell, mCell, rCell) and ConsumeBypassedCell(lCell, mCell, rCell))
      }
  }

  def completeLBypass[A]: (CellContent[A], CompleteLBypass[A]) => (Option[CellContent[A]], ActionResult) = {
    (rContent, cells) =>
      val CompleteLBypass(lCell, mCell, rCell) = cells
      rContent match {
        case LBypassing(`lCell`, `mCell`) =>
          (Some(LFwd(lCell)), AllDone)
        case BiDef(LBypassing(`lCell`, `mCell`), rr) =>
          val (newContent, res) = combine(rCell, LFwd(lCell), rr)
          (Some(newContent), res)
      }
  }

  def consumeBypassedCell[A]: (CellContent[A], ConsumeBypassedCell[A]) => (Option[CellContent[A]], ActionResult) = {
    (mContent, cells) =>
      val ConsumeBypassedCell(lCell, mCell, rCell) = cells
      mContent match {
        case BiDef(LFwd(`lCell`), RFwd(`rCell`)) =>
          (Some(Consumed()), AllDone)
      }
  }

  def awaitDone(
    content: CellContent[Done],
    cellAndListener: (Cell[Done], Either[Throwable, Unit] => Unit),
  ): (CellContent[Done], ActionResult) = {
    val (cell, listener) = cellAndListener
    content match
      case Empty() =>
        (DoneCallback(listener), AllDone)
      case j: JoinOf =>
        (BiDef(j, DoneCallback(listener)), AllDone)
      case LFwd(tgt) =>
        (Consumed(), RefineRFwd(tgt, expectedRTarget = cell, DoneCallback(listener)))
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

/** Role an `A`-cell plays in a `B`-cell to its right. */
enum RoleR[A, B] {
  case Joiner1 extends RoleR[Done, Done]
  case Joiner2 extends RoleR[Done, Done]
}

/** Role a `B`-cell plays in an `A`-cell to its left. */
enum RoleL[A, B] {
  case SelectContestant1 extends RoleL[One |&| One, Pong]
  case SelectContestant2 extends RoleL[One |&| One, Pong]
}
