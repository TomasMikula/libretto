package libretto.scaletto.impl.concurrentcells

import java.util.concurrent.atomic.AtomicReference
import libretto.lambda.UnhandledCase
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
    r.modifyContentWith((l, r), CellContent.unifyInit)

  def rInvertSignal(d: Cell[Done], n: Cell[Need]): ActionResult =
    rInvert(d, Inversion.DoneNeed, n)

  private def rInvert[A, B](src: Cell[A], i: Inversion[A, B], tgt: Cell[B]): ActionResult =
    tgt.modifyContentWith((src, i, tgt), CellContent.rInvertInit)

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

  def joinPong(tgt: Cell[Pong], src1: Cell[Pong], src2: Cell[Pong]): ActionResult =
    tgt.modifyContentWith((tgt, CellContent.JoinPongOf(src1, src2)), CellContent.makeAJoinPongOf)

  def supplyDone(tgt: Cell[Done]): ActionResult =
    tgt.modifyContentWith(tgt, CellContent.supplyDone)

  def select(choiceCell: Cell[One |&| One], contestant1: Cell[Pong], contestant2: Cell[Pong]): ActionResult =
    choiceCell.modifyContentWith(
      (choiceCell, CellContent.SelectOf(contestant1, contestant2)),
      CellContent.makeASelectOf,
    )

  def notifyEither[A, B](src: Cell[A |+| B], pingCell: Cell[Ping], out: Cell[A |+| B]): ActionResult =
    src.modifyContentWith((src, CellContent.RNotifyEither(pingCell, out)), CellContent.notifyEither)

  def notifyChoice[A, B](pongCell: Cell[Pong], tgt: Cell[A |&| B], src: Cell[A |&| B]): ActionResult =
    src.modifyContentWith((CellContent.LNotifyChoice(pongCell, tgt), src), CellContent.notifyChoice)

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

sealed trait CellContent[A] {
  import CellContent._

  final override def toString(): String =
    this match {
      case Empty()            => "Empty()"
      case LFwd(l)            => s"LFwd(${addressOf(l)})"
      case RFwd(r)            => s"RFwd(${addressOf(r)})"
      case LRole(tgt, role)   => s"LLink(${addressOf(tgt)}, $role)"
      case RRole(role, tgt)   => s"RLink($role, ${addressOf(tgt)})"
      case JoinPongOf(p1, p2) => s"JoinPongOf(${addressOf(p1)}, ${addressOf(p2)})"
      case JoinPong1(p1)      => s"JoinPong1(${addressOf(p1)})"
      case JoinPong2(p2)      => s"JoinPong2(${addressOf(p2)})"
      case RInvertSrc(i, tgt) => s"RInvertSrc($i, ${addressOf(tgt)})"
    }

  private def addressOf[X](c: Cell[X]): String =
    "@" + System.identityHashCode(c).toHexString
}
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

  case class RInvertSrc[A, B](inv: Inversion[A, B], tgt: Cell[B]) extends RDefined[A]
  case class RInvertTgt[A, B](src: Cell[A], inv: Inversion[A, B]) extends RDefined[B]

  case class BypassingL[A, B, C](
    newTgt: Cell[A],
    newLink: Link[A, C],
    oldTgt: Cell[B],
    oldLink: Link[B, C],
  ) extends LDefined[C]
  @deprecated
  case class LBypassing[A](newTgt: Cell[A], oldTgt: Cell[A]) extends LDefined[A]
  @deprecated
  case class LBypassingTo[A, B](newTgt: Cell[A], newRole: RoleL[A, B], oldTgt: Cell[B]) extends LDefined[B]

  case class RInvertSrcBypassingTgt[A, B](rInv: Inversion[A, B], oldTgt: Cell[B], newTgt: Cell[B]) extends RDefined[A]
  case class RInvertTgtBypassingSrc[A, B](newTgt: Cell[A], oldTgt: Cell[A], rInv: Inversion[A, B]) extends RDefined[B]

  case class LRole[A, B](tgt: Cell[A], role: RoleL[A, B]) extends LDefined[B]
  case class RRole[A, B](role: RoleR[A, B], tgt: Cell[B]) extends RDefined[A]

  case object DoneSupplied extends LComplete[Done]
  case class DoneCallback(f: Either[Throwable, Unit] => Unit) extends RComplete[Done]

  case object PongSupplied extends RComplete[Pong]

  case class LSplit[A1, A2](cell1: Cell[A1], cell2: Cell[A2]) extends LComplete[A1 |*| A2]
  case class RSplit[A1, A2](cell1: Cell[A1], cell2: Cell[A2]) extends RComplete[A1 |*| A2]

  case class InjectedL[A, B](value: Cell[A]) extends LComplete[A |+| B]
  case class InjectedR[A, B](value: Cell[B]) extends LComplete[A |+| B]
  case class EitherSwitch[A, B, C](f: A -⚬ C, g: B -⚬ C, tgt: Cell[C]) extends RDefined[A |+| B]
  case class EitherCallback[A, B](f: Either[Throwable, Either[Cell[A], Cell[B]]] => Unit) extends RComplete[A |+| B]

  case class ChosenL[A, B](resultCell: Cell[A]) extends RComplete[A |&| B]
  case class ChosenR[A, B](resultCell: Cell[B]) extends RComplete[A |&| B]
  case class ChooseFrom[A, B, C](tgt: Cell[A], f: A -⚬ B, g: A -⚬ C) extends LDefined[B |&| C]
  case class ChoiceWith[A, B, C](tgt: Cell[(A |*| B) |&| (A |*| C)], addendum: Cell[A]) extends LDefined[B |&| C]

  case class JoinOf(src1: Cell[Done], src2: Cell[Done]) extends LDefined[Done]
  case class JoinPongOf(src1: Cell[Pong], src2: Cell[Pong]) extends RDefined[Pong]
  case class JoinPong1(src1: Cell[Pong]) extends RDefined[Pong] // after Pong from src2 has arrived
  case class JoinPong2(src2: Cell[Pong]) extends RDefined[Pong] // after Pong from src1 has arrived

  case class SelectOf(contestant1: Cell[Pong], contestant2: Cell[Pong]) extends RDefined[One |&| One]

  case class RNotifyEither[A, B](notificationCell: Cell[Ping], outCell: Cell[A |+| B]) extends RDefined[A |+| B]
  case class LNotifyChoice[A, B](
    notification: Cell[Pong] | LBypassingPong,
    tgt: Cell[A |&| B] | LBypassing[A |&| B],
  ) extends LDefined[A |&| B] {
    def notificationCell: Cell[Pong] =
      notification match
        case c: Cell[Pong]             => c
        case LBypassingPong(newTgt, _) => newTgt

    def tgtCell: Cell[A |&| B] =
      tgt match
        case c: Cell[A |&| B]       => c
        case l: LBypassing[A |&| B] => l.newTgt
  }
  case class LBypassingPong(newTgt: Cell[Pong], oldTgt: Cell[Pong])

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
      * @param role the role `src` plays in `receiver`
      * @param receiver must already know that it will be fed from `src`
      */
    case class DirectToR[A, B](src: Cell[A], role: RoleR[A, B], receiver: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        src.modifyContentWith((src, RRole(role, receiver)), CellContent.directToR)
    }

    /** An action to refine `src` by pointing it at `receiver` to its left.
      *
      * @param src must be yet unconnected to the left
      * @param role the role `src` plays in `receiver`
      * @param receiver must already know that it will be fed from `src`
      */
    case class DirectToL[A, B](receiver: Cell[A], role: RoleL[A, B], src: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        src.modifyContentWith((LRole(receiver, role), src), CellContent.directToL)
    }

    case class RefineLFwd[A](cell: Cell[A], expectedLTarget: Cell[A], payload: LComplete[A]) extends Instruction {
      override def execute(): ActionResult =
        cell.modifyContentWith(this, CellContent.refineLFwd)
    }

    case class RefineRFwd[A](cell: Cell[A], expectedRTarget: Cell[A], payload: RComplete[A]) extends Instruction {
      override def execute(): ActionResult =
        cell.modifyContentWith(this, CellContent.refineRFwd)
    }

    case class RefineRLink[A, B](cell: Cell[A], rRole: RoleR[A, B], expectedRTarget: Cell[B], payload: RComplete[A]) extends Instruction {
      override def execute(): ActionResult =
        cell.modifyContentWith(this, CellContent.refineRLink)
    }

    case class RefineRPart[A, B](cell: Cell[A], lRole: RoleL[A, B], expectedRTarget: Cell[B], payload: RComplete[B]) extends Instruction {
      override def execute(): ActionResult =
        cell.modifyContentWith(this, CellContent.refineRPart)
    }

    case class RReciprocateForward[A](src: Cell[A], tgt: Cell[A]) extends Instruction {
      override def execute(): ActionResult =
        src.modifyContentOptWith((src, tgt), CellContent.rReciprocateFwd)
    }

    case class RReciprocateRInvert[A, B](src: Cell[A], inv: Inversion[A, B], tgt: Cell[B]) extends Instruction {
      override def execute(): ActionResult = ???
    }

    case class ContractCell[A, B, C](
      l: Cell[A],
      lLink: Link[A, B],
      slated: Cell[B],
      rLink: Link[B, C],
      r: Cell[C],
      newLink: Link[A, C],
    ) extends Instruction {
      override def execute(): ActionResult =
        r.modifyContentOptWith(this, CellContent.initContraction)
    }

    @deprecated
    case class ContractBiFwd[A](l: Cell[A], slated: Cell[A], r: Cell[A]) extends Instruction {
      override def execute(): ActionResult =
        r.modifyContentOptWith((l, slated, r), CellContent.initLBypass)
    }

    @deprecated
    case class ContractLFwd[A, B](l: Cell[A], slated: Cell[A], rRel: RoleR[A, B], r: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        r.modifyContentOptWith(this, CellContent.initContractLFwd)
    }

    @deprecated
    case class ContractRFwd[A, B](l: Cell[A], lRel: RoleL[A, B], slated: Cell[B], r: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        r.modifyContentOptWith(this, CellContent.initContractRFwd)
    }

    case class ContractLFwdRInvTgt[A, B](lCell: Cell[A], slated: Cell[A], rInv: Inversion[B, A], src: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        src.modifyContentWith(this, CellContent.initRInvTgtContractionLFwd)
    }

    case class ContractLFwdRInvSrc[A, B](lCell: Cell[A], slated: Cell[A], rInv: Inversion[A, B], tgt: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        tgt.modifyContentOptWith(this, CellContent.initRInvSrcContractionLFwd)
    }

    case class SkipSlatedCell[A, B, C](contraction: ContractCell[A, B, C]) extends Instruction {
      override def execute(): ActionResult = ???
    }

    @deprecated
    case class SkipAhead[A](l: Cell[A], m: Cell[A], r: Cell[A]) extends Instruction {
      override def execute(): ActionResult =
        l.modifyContentOptWith(this, CellContent.skipAhead)
    }

    @deprecated
    case class SkipAheadTo[A, B](l: Cell[A], lRole: RoleL[A, B], slated: Cell[B], r: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        l.modifyContentOptWith(this, CellContent.skipAheadTo)
    }

    @deprecated
    case class SkipAheadLink[A, B](l: Cell[A], slated: Cell[A], rRole: RoleR[A, B], r: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        l.modifyContentOptWith(this, CellContent.skipAheadLink)
    }

    case class SkipAheadToRInvSrc[A, B](
      lCell: Cell[A],
      slatedRInvTgt: Cell[A],
      rInv: Inversion[B, A],
      rInvSrc: Cell[B],
    ) extends Instruction {
      override def execute(): ActionResult =
        lCell.modifyContentOptWith(this, CellContent.skipAheadToRInvSrc)
    }

    case class SkipAheadToRInvTgt[A, B](
      lCell: Cell[A],
      slatedRInvSrc: Cell[A],
      rInv: Inversion[A, B],
      rInvTgt: Cell[B],
    ) extends Instruction {
      override def execute(): ActionResult =
        lCell.modifyContentOptWith(this, CellContent.skipAheadToRInvTgt)
    }

    case class CompleteLBypass[A](l: Cell[A], bypassed: Cell[A], r: Cell[A]) extends Instruction {
      override def execute(): ActionResult =
        r.modifyContentOptWith(this, CellContent.completeLBypass)
    }

    case class CompleteContractRFwd[A, B](l: Cell[A], link: RoleL[A, B], bypassed: Cell[B], r: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        r.modifyContentOptWith(this, CellContent.completeContractRFwd)
    }

    case class CompleteContractLFwd[A, B](l: Cell[A], bypassed: Cell[A], link: RoleR[A, B], r: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        r.modifyContentOptWith(this, CellContent.completeContractLFwd)
    }

    case class CompleteRInvTgtContraction[A, B](lCell: Cell[A], bypassed: Cell[A], invSrc: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        invSrc.modifyContentOptWith(this, CellContent.completeRInvTgtContraction)
    }

    case class CompleteRInvSrcContraction[A, B](lCell: Cell[A], bypassed: Cell[A], invTgt: Cell[B]) extends Instruction {
      override def execute(): ActionResult =
        invTgt.modifyContentOptWith(this, CellContent.completeRInvSrcContraction)
    }

    case class ConsumeBypassedCell[A, B, C](l: Cell[A], bypassed: Cell[B], r: Cell[C]) extends Instruction {
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
        case EitherSwitch(f, g, tgt) =>
          (Consumed(), ConnectionRequest(src, f, tgt))
        case _: LDefined[A |+| B] | Consumed() =>
          throw new IllegalStateException(s"The target cell is already left-connected: $tgt")
      }
  }

  def injectR[A, B]: (CellContent[A |+| B], (Cell[B], Cell[A |+| B])) => (CellContent[A |+| B], ActionResult) = {
    (tgtContent, cells) =>
      val (srcCell, eitherCell) = cells
      tgtContent match {
        case Empty() =>
          (InjectedR(srcCell), AllDone)
        case EitherCallback(f) =>
          (Consumed(), CallbackTriggered(f, Right(Right(srcCell))))
        case EitherSwitch(f, g, tgtCell) =>
          (Consumed(), ConnectionRequest(srcCell, g, tgtCell))
        case RFwd(tgt1) =>
          (Consumed(), RefineLFwd(tgt1, expectedLTarget = eitherCell, InjectedR(srcCell)))
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
        case l: LBypassing[A |&| B] =>
          (BiDef(l, ChosenR(resultCell)), AllDone)
        case l: LNotifyChoice[A, B] =>
          val followUp =
            RefineRLink(l.notificationCell, RoleR.ChoiceNotification(), expectedRTarget = choiceCell, PongSupplied) and
            RefineRLink(l.tgtCell, RoleR.NotifyChoiceTgt(), expectedRTarget = choiceCell, ChosenR(resultCell))
          (Consumed(), followUp)
      }
  }

  def chooseFrom[A, B, C]: (CellContent[B |&| C], ChooseFrom[A, B, C]) => (CellContent[B |&| C], ActionResult) = {
    (src, ch) =>
      src match {
        case Empty() => (ch, AllDone)
        case rFwd @ RFwd(_) => (BiDef(ch, rFwd), AllDone)
        case ChosenL(rTgt)  => (Consumed(), ConnectionRequest(ch.tgt, ch.f, rTgt))
        case ChosenR(rTgt)  => (Consumed(), ConnectionRequest(ch.tgt, ch.g, rTgt))
      }
  }

  def choiceWith[A, B, C]: (CellContent[B |&| C], ChoiceWith[A, B, C]) => (CellContent[B |&| C], ActionResult) = {
    (src, ch) =>
      src match {
        case Empty() => (ch, AllDone)
        case rFwd @ RFwd(_) => (BiDef(ch, rFwd), AllDone)
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

  val makeAJoinPongOf: (CellContent[Pong], (Cell[Pong], JoinPongOf)) => (CellContent[Pong], ActionResult) = {
    (content, cellAndJoiners) =>
      import RoleL.{JoinerPong1, JoinerPong2}

      val (self, joiners) = cellAndJoiners
      content match {
        case Empty() =>
          val followUp =
            DirectToL(self, JoinerPong1, joiners.src1) and
            DirectToL(self, JoinerPong2, joiners.src2)
          (joiners, followUp)
        case l: LDefined[Pong] =>
          val followUp =
            DirectToL(self, JoinerPong1, joiners.src1) and
            DirectToL(self, JoinerPong2, joiners.src2)
          (BiDef(l, joiners), followUp)
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

  def notifyEither[A, B]: (CellContent[A |+| B], (Cell[A |+| B], RNotifyEither[A, B])) => (CellContent[A |+| B], ActionResult) = {
    (srcContent, cellAndPayload) =>
      import RoleL.{EitherNotification, NotifyEitherTgt}

      val (self, payload) = cellAndPayload
      srcContent match {
        case Empty() =>
          val followUp =
            DirectToL(self, EitherNotification(), payload.notificationCell) and
            DirectToL(self, NotifyEitherTgt(), payload.outCell)
          (payload, followUp)
      }
  }

  def notifyChoice[A, B]: (CellContent[A |&| B], (LNotifyChoice[A, B], Cell[A |&| B])) => (CellContent[A |&| B], ActionResult) = {
    (srcContent, payloadAndCell) =>
      import RoleR.{ChoiceNotification, NotifyChoiceTgt}

      val (payload, self) = payloadAndCell
      srcContent match {
        case Empty() =>
          val followUp =
            DirectToR(payload.notificationCell, ChoiceNotification(), self) and
            DirectToR(payload.tgtCell, NotifyChoiceTgt(), self)
          (payload, followUp)
        case cl @ ChosenL(_) =>
          val followUp =
            RefineRLink(payload.notificationCell, ChoiceNotification(), self, PongSupplied) and
            RefineRLink(payload.tgtCell, NotifyChoiceTgt(), self, cl)
          (Consumed(), followUp)
      }
  }

  def directToR[A, B]: (CellContent[A], (Cell[A], RRole[A, B])) => (CellContent[A], ActionResult) = {
    (src, cellAndLink) =>
      val (self, rLink) = cellAndLink
      src match {
        case Empty()                => (rLink, AllDone)
        case l @ LFwd(lTgt)         => (BiDef(l, rLink), ContractLFwd(lTgt, slated = self, rLink.role, rLink.tgt))
        case l: LBypassing[A]       => (BiDef(l, rLink), AllDone)
        case l: JoinOf              => (BiDef(l, rLink), AllDone)
        case l: ChooseFrom[x, y, z] => (BiDef(l, rLink), AllDone)
      }
  }

  def directToL[A, B]: (CellContent[B], (LRole[A, B], Cell[B])) => (CellContent[B], ActionResult) = {
    (src, lLinkSelf) =>
      val (lLink, self) = lLinkSelf
      src match {
        case Empty() => (lLink, AllDone)
        case r @ RFwd(rTgt) => (BiDef(lLink, r), ContractRFwd(lLink.tgt, lLink.role, slated = self, rTgt))
      }
  }

  def unifyInit[A]: (CellContent[A], (Cell[A], Cell[A])) => (CellContent[A], ActionResult) = {
    (rContent, cells) =>
      val (lCell, rCell) = cells
      rContent match {
        case Empty()                 => (LFwd(lCell), RReciprocateForward(lCell, rCell))
        case c: ChosenL[a1, a2]      => (Consumed(), RefineRFwd[a1 |&| a2](lCell, expectedRTarget = rCell, c))
        case c: ChosenR[a1, a2]      => (Consumed(), RefineRFwd[a1 |&| a2](lCell, expectedRTarget = rCell, c))
        case e: EitherCallback[x, y] => (Consumed(), RefineRFwd[x |+| y](lCell, expectedRTarget = rCell, e))
        case r: RSplit[x, y]         => (Consumed(), RefineRFwd[x |*| y](lCell, expectedRTarget = rCell, r))
        case cb: DoneCallback        => (Consumed(), RefineRFwd[Done](lCell, expectedRTarget = rCell, cb))
        case PongSupplied            => (Consumed(), RefineRFwd(lCell, expectedRTarget = rCell, PongSupplied))
        case rFwd: RFwd[a]           => (BiDef(LFwd(lCell), rFwd), ContractBiFwd(lCell, rCell, rFwd.tgt))
        case rLnk @ RRole(role, tgt) => (BiDef(LFwd(lCell), rLnk), ContractLFwd(lCell, rCell, role, tgt))
        case s: SelectOf             => (BiDef(LFwd(lCell), s), RReciprocateForward(lCell, rCell))
        case j: JoinPongOf           => (BiDef(LFwd(lCell), j), RReciprocateForward(lCell, rCell))
      }
  }

  def rReciprocateFwd[A]: (CellContent[A], (Cell[A], Cell[A])) => (Option[CellContent[A]], ActionResult) = {
    (lContent, cells) =>
      val (self, rCell) = cells
      lContent match {
        case Empty()                => (Some(RFwd(rCell)), AllDone)
        case DoneSupplied           => (Some(Consumed()), RefineLFwd(rCell, expectedLTarget = self, DoneSupplied))
        case l: LSplit[x, y]        => (Some(Consumed()), RefineLFwd(rCell, expectedLTarget = self, l))
        case i: InjectedR[x, y]     => (Some(Consumed()), RefineLFwd(rCell, expectedLTarget = self, i))
        case l: LFwd[x]             => (Some(BiDef(l, RFwd(rCell))), ContractBiFwd(l.tgt, slated = self, rCell))
        case l: LRole[x, y]         => (Some(BiDef(l, RFwd(rCell))), ContractRFwd(l.tgt, l.role, slated = self, rCell))
        case l: LBypassingTo[x, y]  => (Some(BiDef(l, RFwd(rCell))), AllDone)
        case j: JoinOf              => (Some(BiDef(j, RFwd(rCell))), AllDone)
        case c: ChooseFrom[x, y, z] => (Some(BiDef(c, RFwd(rCell))), AllDone)
        case c: ChoiceWith[x, y, z] => (Some(BiDef(c, RFwd(rCell))), AllDone)
        case l: LBypassing[x]       => (Some(BiDef(l, RFwd(rCell))), AllDone)

        // overtaken
        case BiDef(_, _)  => (None, AllDone)
        case RSplit(_, _) => (None, AllDone)
        case ChosenR(_)   => (None, AllDone)
        case ChosenL(_)   => (None, AllDone)
        case Consumed()   => (None, AllDone)
      }
  }

  def rInvertInit[A, B]: (CellContent[B], (Cell[A], Inversion[A, B], Cell[B])) => (CellContent[B], ActionResult) = {
    (tgtContent, srcInvTgt) =>
      val (src, inv, tgt) = srcInvTgt
      tgtContent match {
        case Empty()    => (RInvertTgt(src, inv), RReciprocateRInvert(src, inv, tgt))
        case l: LFwd[B] => (BiDef(l, RInvertTgt(src, inv)), ContractLFwdRInvTgt(l.tgt, tgt, inv, src))
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

  def refineRLink[A, B]: (CellContent[A], RefineRLink[A, B]) => (CellContent[A], ActionResult) = {
    (lContent, refinement) =>
      val RefineRLink(self, rRole, expectedRCell, payload) = refinement
      lContent match {
        case r @ RRole(rRole1, rTgt) =>
          if ((rTgt eq expectedRCell) && (rRole1 == rRole))
            (payload, AllDone)
          else
            throw new IllegalStateException(s"Actual $r did not equal expected ${RRole(rRole, expectedRCell)}")
        case BiDef(l, r) =>
          r match {
            case r @ RRole(rRole1, rTgt) =>
              if ((rTgt eq expectedRCell) && (rRole1 == rRole))
                combineLDefinedRComplete(self, l, payload)
              else
                throw new IllegalStateException(s"Actual $r did not equal expected ${RRole(rRole, expectedRCell)}")
          }
        case LFwd(lTgt) =>
          (Consumed(), RefineRFwd(lTgt, expectedRTarget = self, payload))
        case l: LBypassing[A] =>
          (BiDef(l, payload), AllDone)
        case Empty() =>
          (payload, AllDone)
      }
  }

  def refineRPart[A, B]: (CellContent[A], RefineRPart[A, B]) => (CellContent[A], ActionResult) = {
    import RoleL._

    (lContent, refinement) =>
      val RefineRPart(self, lRole, expectedRCell, payload) = refinement
      lContent match {
        case Empty() =>
          throw new IllegalStateException(s"Unexpected empty cell linked to by $lRole from $expectedRCell")
        case BiDef(l, r) =>
          lRole match
            case JoinerPong1 =>
              r match
                case JoinPongOf(src1, src2) =>
                  assert(src1 eq expectedRCell)
                  payload match
                    case PongSupplied =>
                      combine(self, l, JoinPong2(src2))
            case JoinerPong2 =>
              r match
                case JoinPongOf(src1, src2) =>
                  assert(src2 eq expectedRCell)
                  payload match
                    case PongSupplied =>
                      combine(self, l, JoinPong1(src1))
      }
  }

  private def combineLDefinedRComplete[A](self: Cell[A], l: LDefined[A], r: RComplete[A]): (CellContent[A], ActionResult) =
    r match
      case cb @ DoneCallback(listener) =>
        l match
          case DoneSupplied => (Consumed(), CallbackTriggered(listener, Right(())))
          case j: JoinOf    => (BiDef(j, cb), AllDone)
          case LFwd(lTgt)   => (Consumed(), RefineRFwd(lTgt, expectedRTarget = self, cb))
      case cb @ EitherCallback(listener) =>
        l match
          case InjectedL(cell) => (Consumed(), CallbackTriggered(listener, Right(Left(cell))))
          case InjectedR(cell) => (Consumed(), CallbackTriggered(listener, Right(Right(cell))))
      case r @ RSplit(b1, b2) =>
        l match
          case LSplit(a1, a2)   => (Consumed(), UnificationRequest(a1, b1) and UnificationRequest(a2, b2))
          case LFwd(lTgt)       => (Consumed(), RefineRFwd(lTgt, expectedRTarget = self, r))
          case l: LBypassing[A] => (BiDef(l, r), AllDone)
      case cr @ ChosenR(resultCell) =>
        l match
          case ChooseFrom(lTgt, _, g) => (Consumed(), ConnectionRequest(lTgt, g, resultCell))
          case LFwd(lTgt)             => (Consumed(), RefineRFwd(lTgt, expectedRTarget = self, cr))
          case l: LBypassing[A]       => (BiDef(l, r), AllDone)
      case cl @ ChosenL(resultCell) =>
        l match
          case LFwd(lTgt)       => (Consumed(), RefineRFwd(lTgt, expectedRTarget = self, cl))
          case l: LBypassing[A] => (BiDef(l, r), AllDone)
      case PongSupplied =>
        l match
          case LFwd(lTgt)         => (Consumed(), RefineRFwd(lTgt, expectedRTarget = self, PongSupplied))
          case LRole(lTgt, lRole) => (Consumed(), RefineRPart(lTgt, lRole, expectedRTarget = self, PongSupplied))

  private def combineLCompleteRDefined[A](self: Cell[A], l: LComplete[A], r: RDefined[A]): (CellContent[A], ActionResult) =
    l match
      case DoneSupplied =>
        r match
          case RFwd(tgt) => (Consumed(), RefineLFwd(tgt, expectedLTarget = self, DoneSupplied))

  private def combine[A](self: Cell[A], l: LDefined[A], r: RDefined[A]): (CellContent[A], ActionResult) =
    (l, r) match {
      case (lc: LComplete[A], r)                => combineLCompleteRDefined(self, lc, r)
      case (l, rc: RComplete[A])                => combineLDefinedRComplete(self, l, rc)
      case (l: LFwd[A], r: RFwd[A])             => (BiDef(l, r), ContractBiFwd(l.tgt, self, r.tgt))
      case (l: LFwd[A], r: RInvertSrc[A, b])    => (BiDef(l, r), ContractLFwdRInvSrc(l.tgt, self, r.inv, r.tgt))
      case (l: LFwd[A], r: JoinPongOf)          => (BiDef(l, r), AllDone)
      case (l: LRole[x, A], r: RFwd[A])         => (BiDef(l, r), ContractRFwd(l.tgt, l.role, self, r.tgt))
      case (l: LFwd[A], r: RRole[A, x])         => (BiDef(l, r), ContractLFwd(l.tgt, self, r.role, r.tgt))
      case (l @ LFwd(lTgt), r @ JoinPong1(src)) => (BiDef(l, r), ContractCell(lTgt, Fwd(), slated = self, RoleL.JoinerPong1, src, Fwd()))
      case _ =>
        UnhandledCase.raise(s"($l, $r)")
    }

  def initContraction[A, B, C]: (CellContent[C], ContractCell[A, B, C]) => (Option[CellContent[C]], ActionResult) = {
    (rContent, contraction) =>
      val ContractCell(lCell, lLink, slatedCell, rLink, self, newLink) = contraction
      rContent match {
        case Empty() =>
          (Some(BypassingL(lCell, newLink, slatedCell, rLink)), SkipSlatedCell(contraction))
      }
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
        case LBypassing(newTgt, oldTgt) =>
          if (newTgt eq mCell)
            (Some(LBypassing(lCell, mCell)), SkipAhead(lCell, mCell, rCell))
          else // overtaken
            (None, AllDone)
        case BiDef(l, r) =>
          def go(lTgt: Cell[A]): (Option[CellContent[A]], ActionResult) =
            if (lTgt eq mCell) {
              r match
                case RFwd(_) | RRole(_, _) => // obstructed by higher-priority task (rCell is being bypassed)
                  (None, AllDone)
                case j: JoinPongOf =>
                  (Some(BiDef(LBypassing(lCell, mCell), j)), SkipAhead(lCell, mCell, rCell))
            } else { // overtaken
              (None, AllDone)
            }

          l match
            case LFwd(tgt)             => go(tgt)
            case LBypassing(newTgt, _) => go(newTgt)

        // overtaken
        case Consumed()   => (None, AllDone)
        case DoneSupplied => (None, AllDone)
      }
  }

  def initContractRFwd[A, B]: (CellContent[B], ContractRFwd[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (rContent, contraction) =>
      val ContractRFwd(lCell, link, slatedCell, self) = contraction
      rContent match {
        case Empty() =>
          (Some(LBypassingTo(lCell, link, slatedCell)), SkipAheadTo(lCell, link, slatedCell, self))
        case LFwd(lTgt) =>
          if (lTgt eq slatedCell)
            (Some(LBypassingTo(lCell, link, slatedCell)), SkipAheadTo(lCell, link, slatedCell, self))
          else // overtaken
            (None, AllDone)
        case LBypassing(newTgt, _) =>
          if (newTgt eq slatedCell)
            (Some(LBypassingTo(lCell, link, slatedCell)), SkipAheadTo(lCell, link, slatedCell, self))
          else // overtaken
            (None, AllDone)
        case BiDef(rl, rr) =>
          def go(lTgt: Cell[B]): (Option[CellContent[B]], ActionResult) =
            if (lTgt eq slatedCell) {
              rr match {
                case RFwd(_) | RRole(_, _) => // obstructed by higher-priority task (the `self` cell is being bypassed)
                  (None, AllDone)
              }
            } else { // overtaken
              (None, AllDone)
            }

          rl match
            case LFwd(tgt) => go(tgt)
        case r: RRole[B, c] =>
          (Some(BiDef(LBypassingTo(lCell, link, slatedCell), r)), SkipAheadTo(lCell, link, slatedCell, self))
      }
  }

  def initContractLFwd[A, B]: (CellContent[B], ContractLFwd[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (rContent, contraction) =>
      val ContractLFwd(lCell, slatedCell, rRole, self) = contraction
      rContent match {
        case l: LNotifyChoice[x, y] =>
          import RoleR._
          rRole match {
            case ChoiceNotification() =>
              if (l.notificationCell eq slatedCell)
                ( Some(LNotifyChoice(LBypassingPong(lCell, slatedCell), l.tgt))
                , SkipAheadLink(lCell, slatedCell, rRole, self)
                )
              else // overtaken
                (None, AllDone)
            case NotifyChoiceTgt() =>
              if (l.tgtCell eq slatedCell)
                ( Some(LNotifyChoice(l.notification, LBypassing[x |&| y](lCell, slatedCell)))
                , SkipAheadLink(lCell, slatedCell, rRole, self)
                )
              else // overtaken
                (None, AllDone)
          }
        case Consumed() =>
          (None, AllDone)
        case LRole(_, lRole) =>
          throw new IllegalStateException(s"Unexpected reciprocal roles: $rRole <-> $lRole")
      }
  }

  def initRInvTgtContractionLFwd[A, B]: (CellContent[B], ContractLFwdRInvTgt[A, B]) => (CellContent[B], ActionResult) = {
    (invSrcContent, contraction) =>
      val ContractLFwdRInvTgt(lCell, slatedRInvTgt, rInv, rInvSrc) = contraction
      invSrcContent match {
        case Empty() =>
          ( RInvertSrcBypassingTgt(rInv, oldTgt = slatedRInvTgt, newTgt = lCell)
          , SkipAheadToRInvSrc(lCell, slatedRInvTgt, rInv, rInvSrc)
          )
        case l: LFwd[B] =>
          ( BiDef(l, RInvertSrcBypassingTgt(rInv, oldTgt = slatedRInvTgt, newTgt = lCell))
          , SkipAheadToRInvSrc(lCell, slatedRInvTgt, rInv, rInvSrc)
          )
      }
  }

  def initRInvSrcContractionLFwd[A, B]: (CellContent[B], ContractLFwdRInvSrc[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (invTgtContent, contraction) =>
      val ContractLFwdRInvSrc(lCell, slatedInvSrc, inv, invTgt) = contraction
      invTgtContent match {
        case Empty() =>
          ( Some(RInvertTgtBypassingSrc(newTgt = lCell, oldTgt = slatedInvSrc, inv))
          , SkipAheadToRInvTgt(lCell, slatedInvSrc, inv, invTgt)
          )
        case RInvertTgt(src, inv1) =>
          assert(inv1 == inv, s"Unexpected inversion $inv1, expected $inv")
          if (src eq slatedInvSrc)
            ( Some(RInvertTgtBypassingSrc(newTgt = lCell, slatedInvSrc, inv))
            , SkipAheadToRInvTgt(lCell, slatedInvSrc, inv, invTgt)
            )
          else // overtaken
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
        case l @ LFwd(lTgt) =>
          (Some(BiDef(l, RFwd(rCell))), ContractBiFwd(lTgt, lCell, rCell) and ConsumeBypassedCell(lCell, mCell, rCell))
        case l @ LRole(lTgt, lRole) =>
          (Some(BiDef(l, RFwd(rCell))), ContractRFwd(lTgt, lRole, slated = lCell, rCell) and ConsumeBypassedCell(lCell, mCell, rCell))
        case l: LBypassing[A] =>
          (Some(BiDef(l, RFwd(rCell))), CompleteLBypass(lCell, mCell, rCell) and ConsumeBypassedCell(lCell, mCell, rCell))
        case c: ChooseFrom[x, a1, a2] =>
          (Some(BiDef(c, RFwd(rCell))), CompleteLBypass(lCell, mCell, rCell) and ConsumeBypassedCell(lCell, mCell, rCell))
      }
  }

  def skipAheadTo[A, B]: (CellContent[A], SkipAheadTo[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (lContent, payload) =>
      val SkipAheadTo(lCell, lRole, slatedCell, rCell) = payload
      lContent match {
        case BiDef(ll, lr) =>
          lr match {
            case JoinPongOf(src1, src2) =>
              import RoleL.{JoinerPong1, JoinerPong2}
              lRole match {
                case JoinerPong1 =>
                  if (src1 eq slatedCell)
                    val followUp =
                      CompleteContractRFwd(lCell, lRole, slatedCell, rCell) and
                      ConsumeBypassedCell(lCell, slatedCell, rCell)
                    (Some(BiDef(ll, JoinPongOf(rCell, src2))), followUp)
                  else // overtaken
                    (None, AllDone)
                case JoinerPong2 =>
                  if (src2 eq slatedCell)
                    val followUp =
                      CompleteContractRFwd(lCell, lRole, slatedCell, rCell) and
                      ConsumeBypassedCell(lCell, slatedCell, rCell)
                    (Some(BiDef(ll, JoinPongOf(src1, rCell))), followUp)
                  else // overtaken
                    (None, AllDone)
              }
            case RRole(rRole, _) =>
              throw new IllegalStateException(s"Unexpected reciprocal roles: $rRole <-> $lRole")
          }
        case Empty() | _: LDefined[A] =>
          throw new IllegalStateException(s"Unexpected right-unconnected cell ($lContent) linked to by $lRole from $slatedCell")
      }
  }

  def skipAheadLink[A, B]: (CellContent[A], SkipAheadLink[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (lContent, payload) =>
      val SkipAheadLink(lCell, slatedCell, rRole, rCell) = payload
      lContent match {
        case Empty() =>
          val followUp =
            CompleteContractLFwd(lCell, slatedCell, rRole, rCell) and
            ConsumeBypassedCell(lCell, slatedCell, rCell)
          (Some(RRole(rRole, rCell)), followUp)
        case BiDef(l, r) =>
          r match {
            case RFwd(tgt) =>
              if (tgt eq slatedCell)
                val followUp =
                  CompleteContractLFwd(lCell, slatedCell, rRole, rCell) and
                  ConsumeBypassedCell(lCell, slatedCell, rCell)
                (Some(RRole(rRole, rCell)), followUp)
              else // overtaken
                (None, AllDone)
          }
      }
  }

  def skipAheadToRInvSrc[A, B]: (CellContent[A], SkipAheadToRInvSrc[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (lContent, payload) =>
      val SkipAheadToRInvSrc(lCell, slatedCell, inversion, invSrc) = payload
      lContent match {
        case Empty() =>
          val followUp =
            CompleteRInvTgtContraction(lCell, slatedCell, invSrc) and
            ConsumeBypassedCell(lCell, slatedCell, invSrc)
          (Some(RInvertTgt(invSrc, inversion)), followUp)
        case RFwd(rTgt) =>
          if (rTgt eq slatedCell)
            val followUp =
              CompleteRInvTgtContraction(lCell, slatedCell, invSrc) and
              ConsumeBypassedCell(lCell, slatedCell, invSrc)
            (Some(RInvertTgt(invSrc, inversion)), followUp)
          else // overtaken
            (None, AllDone)
      }
  }

  def skipAheadToRInvTgt[A, B]: (CellContent[A], SkipAheadToRInvTgt[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (lContent, payload) =>
      val SkipAheadToRInvTgt(lCell, slatedCell, inversion, invTgt) = payload
      lContent match {
        case Empty() =>
          val followUp =
            CompleteRInvSrcContraction(lCell, slatedCell, invTgt) and
            ConsumeBypassedCell(lCell, slatedCell, invTgt)
          (Some(RInvertSrc(inversion, invTgt)), followUp)
        case RFwd(rTgt) =>
          if (rTgt eq slatedCell)
            val followUp =
              CompleteRInvSrcContraction(lCell, slatedCell, invTgt) and
              ConsumeBypassedCell(lCell, slatedCell, invTgt)
            (Some(RInvertSrc(inversion, invTgt)), followUp)
          else // overtaken
            (None, AllDone)
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

  def completeContractRFwd[A, B]: (CellContent[B], CompleteContractRFwd[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (rContent, payload) =>
      val CompleteContractRFwd(lCell, lLink, bypassedCell, rCell) = payload
      rContent match {
        case LBypassingTo(`lCell`, `lLink`, `bypassedCell`) =>
          (Some(LRole(lCell, lLink)), AllDone)
        case BiDef(l, r) =>
          l match {
            case LBypassingTo(`lCell`, `lLink`, `bypassedCell`) =>
              val (content, action) = combine(rCell, LRole(lCell, lLink), r)
              (Some(content), action)
          }
      }
  }

  def completeContractLFwd[A, B]: (CellContent[B], CompleteContractLFwd[A, B]) => (Option[CellContent[B]], ActionResult) = {
    import RoleR._

    (rContent, payload) =>
      val CompleteContractLFwd(lCell, bypassedCell, rRole, rCell) = payload
      rContent match {
        case l: LNotifyChoice[x, y] =>
          rRole match {
            case ChoiceNotification() =>
              l.notification match
                case LBypassingPong(`lCell`, _) => (Some(LNotifyChoice(lCell, l.tgt)), AllDone)
                case _                          => (None, AllDone) // overtaken
            case NotifyChoiceTgt() =>
              ???
          }
        case Consumed() =>
          (None, AllDone)
      }
  }

  def completeRInvTgtContraction[A, B]: (CellContent[B], CompleteRInvTgtContraction[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (invSrcContent, payload) =>
      val CompleteRInvTgtContraction(lCell, slatedCell, self) = payload
      invSrcContent match {
        case RInvertSrcBypassingTgt(rInv, _, newTgt) =>
          if (newTgt eq lCell) {
            (Some(RInvertSrc(rInv, newTgt)), AllDone)
          } else { // overtaken
            (None, AllDone)
          }
        case BiDef(l, r) =>
          r match {
            case RInvertSrcBypassingTgt(rInv, _, newTgt) =>
              if (newTgt eq lCell) {
                val (content, action) = combine(self, l, RInvertSrc(rInv, newTgt))
                (Some(content), action)
              } else { // overtaken
                (None, AllDone)
              }
          }
      }
  }

  def completeRInvSrcContraction[A, B]: (CellContent[B], CompleteRInvSrcContraction[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (invTgtContent, payload) =>
      val CompleteRInvSrcContraction(lCell, bypassedCell, self) = payload
      invTgtContent match {
        case RInvertTgtBypassingSrc(newTgt, _, rInv) =>
          if (newTgt eq lCell) {
            (Some(RInvertTgt(newTgt, rInv)), AllDone)
          } else { // overtaken
            (None, AllDone)
          }
      }
  }

  def consumeBypassedCell[A, B, C]: (CellContent[B], ConsumeBypassedCell[A, B, C]) => (Option[CellContent[B]], ActionResult) = {
    (mContent, cells) =>
      val ConsumeBypassedCell(lCell, mCell, rCell) = cells
      mContent match {
        case BiDef(l, r) =>
          // check that `l` still points to `lCell`
          l match {
            case LFwd(`lCell`) =>
            case LRole(`lCell`, _) =>
          }
          // check that `r` still points to `rCell`
          r match {
            case RFwd(`rCell`) =>
            case RRole(_, `rCell`) =>
            case RInvertTgt(`rCell`, _) =>
            case RInvertSrc(_, `rCell`) =>
          }
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
      case l: LBypassing[Done] =>
        (BiDef(l, DoneCallback(listener)), AllDone)
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

sealed trait Link[A, B]

case class Fwd[A]() extends Link[A, A]

/** Role an `A`-cell plays in a `B`-cell to its right. */
enum RoleR[A, B] extends Link[A, B] {
  case Joiner1 extends RoleR[Done, Done]
  case Joiner2 extends RoleR[Done, Done]
  case ChoiceNotification[A, B]() extends RoleR[Pong, A |&| B]
  case NotifyChoiceTgt[A, B]() extends RoleR[A |&| B, A |&| B]
}

/** Role a `B`-cell plays in an `A`-cell to its left. */
enum RoleL[A, B] extends Link[A, B] {
  case JoinerPong1 extends RoleL[Pong, Pong]
  case JoinerPong2 extends RoleL[Pong, Pong]
  case SelectContestant1 extends RoleL[One |&| One, Pong]
  case SelectContestant2 extends RoleL[One |&| One, Pong]
  case EitherNotification[A, B]() extends RoleL[A |+| B, Ping]
  case NotifyEitherTgt[A, B]() extends RoleL[A |+| B, A |+| B]
}

enum Iso[A, B] {
  case Id[A]() extends Iso[A, A]
  case NeedInvDone extends Iso[Need, -[Done]]
  case InvDoneNeed extends Iso[-[Done], Need]
  case PongInvPing extends Iso[Pong, -[Ping]]
  case InvPingPong extends Iso[-[Ping], Pong]

  def reverse: Iso[B, A] =
    this match
      case Id() => Id()
      case NeedInvDone => InvDoneNeed
      case InvDoneNeed => NeedInvDone
      case PongInvPing => InvPingPong
      case InvPingPong => PongInvPing

  def andThen[C](that: Iso[B, C]): Iso[A, C] =
    (this, that) match
      case (Id(), that) => that
      case (thiz, Id()) => thiz
      case (InvDoneNeed, NeedInvDone) => Id()
      case (NeedInvDone, InvDoneNeed) => Id()
      case (InvPingPong, PongInvPing) => Id()
      case (PongInvPing, InvPingPong) => Id()
}

enum Inversion[A, B] {
  case DoneNeed extends Inversion[Done, Need]
  case PingPong extends Inversion[Ping, Pong]
  case Universal[A]() extends Inversion[A, -[A]]

  def alsoTo[X](that: Inversion[A, X]): Iso[B, X] =
    (this, that) match {
      case (DoneNeed, DoneNeed)       => Iso.Id()
      case (PingPong, PingPong)       => Iso.Id()
      case (Universal(), Universal()) => Iso.Id()
      case (DoneNeed, Universal())    => Iso.NeedInvDone
      case (Universal(), DoneNeed)    => Iso.InvDoneNeed
      case (PingPong, Universal())    => Iso.PongInvPing
      case (Universal(), PingPong)    => Iso.InvPingPong
    }

  def alsoFrom[X](that: Inversion[X, B]): A =:= X =
    (this, that) match {
      case (DoneNeed, DoneNeed)       => summon
      case (PingPong, PingPong)       => summon
      case (Universal(), Universal()) => summon
    }
}
