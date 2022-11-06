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
  import ActionResult.{ChooseL, ChooseR, InjectL, InjectR, LInvert, PropagateLCompletionRight, SupplyDone, SupplyPing}

  def apply[A](content: CellContent[A]): Cell[A] =
    new AtomicReference(content)

  def empty[A]: Cell[A] =
    Cell(CellContent.Empty())

  def one: Cell[One] =
    empty[One]

  def lsplit[A, B](cell: Cell[A |*| B]): (Cell[A], Cell[B], ActionResult) =
    cell.modifyContentWith(cell, CellContent.lsplit)

  def lsplitInv[A, B](a: Cell[-[A]], b: Cell[-[B]], cell: Cell[-[A |*| B]]): ActionResult =
    cell.modifyContentWith((CellContent.LSplitInv(a, b), cell), CellContent.lsplitInv)

  def rsplit[A, B](cell: Cell[A |*| B]): (Cell[A], Cell[B], ActionResult) =
    cell.modifyContentWith(cell, CellContent.rsplit)

  def rsplitInv[A, B](cell: Cell[-[A |*| B]], a: Cell[-[A]], b: Cell[-[B]]): ActionResult =
    cell.modifyContentWith((cell, CellContent.RSplitInv(a, b)), CellContent.rsplitInv)

  def unify[A](l: Cell[A], r: Cell[A]): ActionResult =
    r.modifyContentWith((l, r), CellContent.unifyInit)

  def strengthenPing(src: Cell[Ping], tgt: Cell[Done]): ActionResult =
    tgt.modifyContentWith((src, tgt), CellContent.strengthenPing)

  def rInvertSignal(d: Cell[Done], n: Cell[Need]): ActionResult =
    rInvert(d, Inversion.DoneNeed, n)

  def rInvertPingPong(src: Cell[Ping], tgt: Cell[Pong]): ActionResult =
    rInvert(src, Inversion.PingPong, tgt)

  def backvert[A](p: Cell[A], n: Cell[-[A]]): ActionResult =
    rInvert(p, Inversion.Universal[A](), n)

  private def rInvert[A, B](src: Cell[A], i: Inversion[A, B], tgt: Cell[B]): ActionResult =
    tgt.modifyContentWith((src, i, tgt), CellContent.rInvertInit)

  def lInvertSignal(n: Cell[Need], d: Cell[Done]): ActionResult =
    lInvert(n, Inversion.DoneNeed, d)

  def lInvertPongPing(src: Cell[Pong], tgt: Cell[Ping]): ActionResult =
    lInvert(src, Inversion.PingPong, tgt)

  def forevert[A](n: Cell[-[A]], p: Cell[A]): ActionResult =
    lInvert(n, Inversion.Universal[A](), p)

  private def lInvert[A, B](src: Cell[B], i: Inversion[A, B], tgt: Cell[A]): ActionResult =
    LInvert(src, i, tgt).execute()

  def injectL[A, B](src: Cell[A], tgt: Cell[A |+| B]): ActionResult =
    InjectL(src, tgt).execute()

  def injectR[A, B](src: Cell[B], tgt: Cell[A |+| B]): ActionResult =
    InjectR(src, tgt).execute()

  def either[A, B, C](src: Cell[A |+| B], f: A -⚬ C, g: B -⚬ C, tgt: Cell[C]): ActionResult =
    src.modifyContentWith(CellContent.EitherSwitch(f, g, tgt), CellContent.eitherSwitch)

  def eitherWith[A, B, C](addendum: Cell[A], src: Cell[B |+| C], tgt: Cell[(A |*| B) |+| (A |*| C)]): ActionResult =
    src.modifyContentWith(CellContent.EitherWith(addendum, tgt), CellContent.eitherWith)

  def chooseL[A, B](choiceCell: Cell[A |&| B], resultCell: Cell[A]): ActionResult =
    ChooseL(choiceCell, resultCell).execute()

  def chooseR[A, B](choiceCell: Cell[A |&| B], resultCell: Cell[B]): ActionResult =
    ChooseR(choiceCell, resultCell).execute()

  def choice[A, B, C](tgt: Cell[A], f: A -⚬ B, g: A -⚬ C, src: Cell[B |&| C]): ActionResult =
    src.modifyContentWith(CellContent.ChooseFrom(tgt, f, g), CellContent.chooseFrom)

  def choiceWith[A, B, C](tgt: Cell[(A |*| B) |&| (A |*| C)], addendum: Cell[A], src: Cell[B |&| C]): ActionResult =
    src.modifyContentWith(CellContent.ChoiceWith(tgt, addendum), CellContent.choiceWith)

  def join(src1: Cell[Done], src2: Cell[Done], tgt: Cell[Done]): ActionResult =
    tgt.modifyContentWith((tgt, CellContent.JoinOf(src1, src2)), CellContent.makeAJoinOf)

  def joinNeed(tgt: Cell[Need], src1: Cell[Need], src2: Cell[Need]): ActionResult =
    tgt.modifyContentWith((tgt, CellContent.JoinNeedOf(src1, src2)), CellContent.makeAJoinNeedOf)

  def joinPong(tgt: Cell[Pong], src1: Cell[Pong], src2: Cell[Pong]): ActionResult =
    tgt.modifyContentWith((tgt, CellContent.JoinPongOf(src1, src2)), CellContent.makeAJoinPongOf)

  def supplyDone(tgt: Cell[Done]): ActionResult =
    SupplyDone(tgt).execute()

  def supplyPing(tgt: Cell[Ping]): ActionResult =
    SupplyPing(tgt).execute()

  def supplyPong(tgt: Cell[Pong]): ActionResult =
    tgt.modifyContentWith(tgt, CellContent.supplyPong)

  def select(choiceCell: Cell[One |&| One], contestant1: Cell[Pong], contestant2: Cell[Pong]): ActionResult =
    choiceCell.modifyContentWith(
      (choiceCell, CellContent.SelectOf(contestant1, contestant2)),
      CellContent.makeASelectOf,
    )

  def notifyEither[A, B](src: Cell[A |+| B], pingCell: Cell[Ping], out: Cell[A |+| B]): ActionResult =
    src.modifyContentWith((src, CellContent.RNotifyEither(pingCell, out)), CellContent.notifyEither)

  def notifyDone(src: Cell[Done], pingCell: Cell[Ping], tgt: Cell[Done]): ActionResult =
    src.modifyContentWith((src, CellContent.RNotifyDone(pingCell, tgt)), CellContent.notifyDone)

  def notifyNeed(pongCell: Cell[Pong], tgt: Cell[Need], src: Cell[Need]): ActionResult =
    src.modifyContentWith((CellContent.LNotifyNeed(pongCell, tgt), src), CellContent.notifyNeed)

  def notifyChoice[A, B](pongCell: Cell[Pong], tgt: Cell[A |&| B], src: Cell[A |&| B]): ActionResult =
    src.modifyContentWith((CellContent.LNotifyChoice(pongCell, tgt), src), CellContent.notifyChoice)

  def injectLOnPing[A, B](pingCell: Cell[Ping], injected: Cell[A], tgt: Cell[A |+| B]): ActionResult =
    tgt.modifyContentWith((pingCell, injected, tgt), CellContent.injectLOnPing)

  def mapVal[A, B](src: Cell[Val[A]], f: A => B, tgt: Cell[Val[B]]): ActionResult =
    src.modifyContentWith((src, f, tgt), CellContent.mapVal)

  def splitVal[A, B](src: Cell[Val[(A, B)]], tgt1: Cell[Val[A]], tgt2: Cell[Val[B]]): ActionResult =
    src.modifyContentWith((src, tgt1, tgt2), CellContent.splitVal)

  def zipVal[A, B](src1: Cell[Val[A]], src2: Cell[Val[B]], tgt: Cell[Val[(A, B)]]): ActionResult =
    tgt.modifyContentWith((src1, src2, tgt), CellContent.zipVal)

  def constVal[A](trigger: Cell[Done], value: A, tgt: Cell[Val[A]]): ActionResult =
    trigger.modifyContentWith((trigger, value, tgt), CellContent.constVal)

  def neglect[A](src: Cell[Val[A]], tgt: Cell[Done]): ActionResult =
    src.modifyContentWith((src, tgt), CellContent.neglect)

  def deliverValRight[A, B](src: Cell[A], value: B, tgt: Cell[Val[B]]): ActionResult =
    PropagateLCompletionRight(src, CellContent.ValSupplied(value), tgt).execute()

  def liftEither[A, B](src: Cell[Val[Either[A, B]]], tgt: Cell[Val[A] |+| Val[B]]): ActionResult =
    src.modifyContentWith((src, tgt), CellContent.liftEither)

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

  def crashFromLeft[A, B](origin: Cell[A], e: Throwable, tgt: Cell[B]): ActionResult =
    tgt.modifyContentOptWith((origin, e, tgt), CellContent.crashFromLeft)

  extension [A](cell: Cell[A]) {
    // def modifyContent[R](f: CellContent[A] => (CellContent[A], R)): R =
    //   cell.modifyOpaque(f)

    def modifyContentOpt[R](f: CellContent[A] => (Option[CellContent[A]], R)): R =
      cell.modifyOpaqueOpt(f)

    def modifyContentWith[B, R](b: B, f: (CellContent[A], B) => (CellContent[A], R)): R =
      cell.modifyOpaqueWith(b, f)

    def modifyContentOptWith[B, R](b: B, f: (CellContent[A], B) => (Option[CellContent[A]], R)) : R =
      cell.modifyOpaqueOptWith(b, f)
  }
}

sealed trait CellContent[A] {
  import CellContent._

  final override def toString(): String = {
    this match {
      case Empty()                 => "Empty()"
      case LFwd(l)                 => s"LFwd(${addr(l)})"
      case RFwd(r)                 => s"RFwd(${addr(r)})"
      case LRole(tgt, role)        => s"LRole(${addr(tgt)}, $role)"
      case RRole(role, tgt)        => s"RRole($role, ${addr(tgt)})"
      case SelectOf(c1, c2)        => s"SelectOf(${addr(c1)}, ${addr(c2)})"
      case JoinOf(c1, c2)          => s"JoinOf(${addr(c1)}, ${addr(c2)})"
      case Join1(c1)               => s"Join1(${addr(c1)})"
      case Join2(c2)               => s"Join2(${addr(c2)})"
      case JoinNeedOf(p1, p2)      => s"JoinNeedOf(${addr(p1)}, ${addr(p2)})"
      case JoinNeed1(p1)           => s"JoinNeed1(${addr(p1)})"
      case JoinNeed2(p2)           => s"JoinNeed2(${addr(p2)})"
      case JoinPongOf(p1, p2)      => s"JoinPongOf(${addr(p1)}, ${addr(p2)})"
      case JoinPong1(p1)           => s"JoinPong1(${addr(p1)})"
      case JoinPong2(p2)           => s"JoinPong2(${addr(p2)})"
      case BiDef(l, r)             => s"BiDef($l, $r)"
      case Slated(l, r)            => s"Slated($l, $r)"
      case DoneSupplied            => "DoneSupplied"
      case PingSupplied            => "PingSupplied"
      case PongSupplied            => "PongSupplied"
      case NeedSupplied            => "NeedSupplied"
      case Consumed()              => "Consumed()"
      case LSplit(c1, c2)          => s"LSplit(${addr(c1)}, ${addr(c2)})"
      case RSplit(c1, c2)          => s"RSplit(${addr(c1)}, ${addr(c2)})"
      case LSplitInv(c1, c2)       => s"LSplitInv(${addr(c1)}, ${addr(c2)})"
      case RSplitInv(c1, c2)       => s"RSplitInv(${addr(c1)}, ${addr(c2)})"
      case ChooseFrom(c, f, g)     => s"ChooseFrom(${addr(c)}, $f, $g)"
      case ChoiceWith(c, a)        => s"ChoiceWith(${addr(c)}, ${addr(a)})"
      case ChosenL(c)              => s"ChosenL(${addr(c)})"
      case ChosenR(c)              => s"ChosenR(${addr(c)})"
      case InjectedL(c)            => s"InjctedL(${addr(c)})"
      case InjectedR(c)            => s"InjctedR(${addr(c)})"
      case EitherCallback(f)       => s"EitherCallback($f)"
      case DoneCallback(f)         => s"DoneCallback($f)"
      case NeedCallback(f)         => s"NeedCallback($f)"
      case LSkippingLeftLeft(x, y) => s"LSkippingLeftLeft(${addr(x)}, ${addr(y)})"
      case LSkippingLeftLRole(x, l, y) => s"LSkippingLeftLRole(${addr(x)}, $l, ${addr(y)})"
      case LSkippingLeftUp(s, i, l)    => s"LSkippingLeftUp(${addr(s)}, $i, ${addr(l)})"
      case LSkippingLeftDown(t, i, l)  => s"LSkippingLeftDown(${addr(t)}, $i, ${addr(l)})"
      case LSkippingUpUp(s0, i, s1, j) => s"LSkippingUpUp(${addr(s0)}, $i, ${addr(s1)}, $j)"
      case RInvertSrc(i, c)        => s"RInvertSrc($i, ${addr(c)})"
      case RInvertTgt(c, i)        => s"RInvertTgt(${addr(c)}, $i)"
      case LInvertSrc(i, c)        => s"LInvertSrc($i, ${addr(c)})"
      case LInvertTgt(c, i)        => s"LInvertTgt(${addr(c)}, $i)"
      case LInvertTgtClaimed(c, i) => s"LInvertTgtClaimed(${addr(c)}, $i)"
      case LInvertSrcPair(c1, c2)  => s"LInvertSrcPair(${addr(c1)}, ${addr(c2)})"
      case LInvertTgtPair(c1, c2)  => s"LInvertTgtPair(${addr(c1)}, ${addr(c2)})"
      case RSkippingDownLeft(i, x, y) => s"RSkippingDownLeft($i, ${addr(x)}, ${addr(y)})"
      case RSkippingUpLeft(x, y, i)   => s"RSkippingUpLeft(${addr(x)}, ${addr(y)}, $i)"
      case LNotifyChoice(n, t)        => s"LNotifyChoice(${addr(n)}, ${addr(t)})"
      case LNotifyNeed(n, t)          => s"LNotifyNeed(${addr(n)}, ${addr(t)})"
      case RNotifyDone(n, t)          => s"RNotifyDone(${addr(n)}, ${addr(t)})"
      case LStrengthenedPing(src)     => s"LStrengthenedPing(${addr(src)})"
      case EitherSwitch(f, g, tgt)    => s"EitherSwitch($f, $g, ${addr(tgt)})"
      case EitherWith(a, c)           => s"EitherWith(${addr(a)}, ${addr(c)})"
      case RNotifyEither(n, t)        => s"RNotifyEither(${addr(n)}, ${addr(t)})"
      case LCompleteInv(r)            => s"LCompleteInv($r)"
      case RCompleteInv(l)            => s"RCompleteInv($l)"
      case InjectLOnPing(tr, c)       => s"InjectLOnPing(${addr(tr)}, ${addr(c)})"
      case RMapValSrc(f, t)           => s"RMapValSrc($f, ${addr(t)})"
      case LValTgt(s)                 => s"LValTgt(${addr(s)})"
      case LDoneTgt(s)                => s"LDoneTgt(${addr(s)})"
      case PropagatingLCompletion(l, r) => s"PropagatingLCompletion($l, $r)"
      case PropagatingRCompletion(l, r) => s"PropagatingRCompletion($l, $r)"
      case RLiftEither(t)               => s"RLiftEither(${addr(t)})"
      case LLiftedEither(s)             => s"LLiftedEither(${addr(s)})"
      case LZipVal(c1, c2)              => s"LZipVal(${addr(c1)}, ${addr(c2)})"
      case LZipVal1(c1, b)              => s"LZipVal1(${addr(c1)}, $b)"
      case LZipVal2(a, c2)              => s"LZipVal2($a, ${addr(c2)})"
      case RSplitVal(c1, c2)            => s"RSplitVal(${addr(c1)}, ${addr(c2)})"
      case RConstVal(v, t)              => s"RConstVal($v, ${addr(t)})"
      case ValSupplied(a)               => s"ValSupplied($a)"
      case LCrashed(e)                  => s"LCrashed($e)"
      case RNeglectVal(t)               => s"RNeglectVal(${addr(t)})"
    }
  }
}
object CellContent {
  case class Empty[A]() extends CellContent[A]
  sealed trait LDefined[A] extends CellContent[A]
  sealed trait RDefined[A] extends CellContent[A]

  /** Cell content with left and right part, such that the parts form a stable conformation. */
  case class BiDef[A](l: LDefined[A], r: RDefined[A]) extends CellContent[A]

  /** Cell content with left and right part, where the collocation of these parts has triggered a reduction.
   *  The cell with this content will soon be consumed, unless the scheduled reduction is obstructed
   *  by a higher-priority activity (i.e. activity originating on the right of this cell).
   */
  case class Slated[A](l: LDefined[A], r: RDefined[A]) extends CellContent[A]

  case class PropagatingLCompletion[A](l: LComplete[A], r: RDefined[A]) extends CellContent[A]
  case class PropagatingRCompletion[A](l: LDefined[A], r: RComplete[A]) extends CellContent[A]

  case class Consumed[A]() extends CellContent[A]

  sealed trait LComplete[A] extends LDefined[A] {
    def rInvert[B](i: Inversion[A, B]): RComplete[B] =
      i match
        case Inversion.DoneNeed =>
          this match
            case DoneSupplied => NeedSupplied
        case Inversion.PingPong =>
          this match
            case PingSupplied => PongSupplied
        case Inversion.Universal() =>
          RCompleteInv(this)

    def rUnInvert[B](i: Inversion[B, A]): RComplete[B] =
      i match
        case Inversion.DoneNeed =>
          this match
            case NeedCallback(f) => DoneCallback(f)
        case Inversion.PingPong =>
          this match
            case DoneSupplied => throw new AssertionError("Impossible: Done =!= Pong")
        case Inversion.Universal() =>
          this match
            case LCompleteInv(src) => src
  }

  sealed trait RComplete[A] extends RDefined[A] {
    def lInvert[B](i: Inversion[A, B]): LComplete[B] =
      i match
        case Inversion.DoneNeed =>
          this match
            case DoneCallback(f) => NeedCallback(f)
        case Inversion.PingPong =>
          this match
            case DoneCallback(f) => throw new AssertionError("Impossible: Done =!= Ping")
        case Inversion.Universal() =>
          LCompleteInv(this)


    def lUnInvert[B](i: Inversion[B, A]): LComplete[B] =
      i match
        case Inversion.DoneNeed =>
          this match
            case NeedSupplied => DoneSupplied
        case Inversion.PingPong =>
          this match
            case PongSupplied => PingSupplied
        case Inversion.Universal() =>
          this match
            case RCompleteInv(src) => src
            case RSplitInv(x, y)   => LInvertTgtPair(x, y)
  }

  case class LCompleteInv[A](src: RComplete[A]) extends LComplete[-[A]]
  case class RCompleteInv[A](src: LComplete[A]) extends RComplete[-[A]]

  case class LFwd[A](tgt: Cell[A]) extends LDefined[A]
  case class RFwd[A](tgt: Cell[A]) extends RDefined[A]

  case class RInvertSrc[A, B](inv: Inversion[A, B], tgt: Cell[B]) extends RDefined[A]
  case class RInvertTgt[A, B](src: Cell[A], inv: Inversion[A, B]) extends RDefined[B]

  case class LInvertSrc[A, B](inv: Inversion[B, A], tgt: Cell[B]) extends LDefined[A]
  case class LInvertTgt[A, B](src: Cell[A], inv: Inversion[B, A]) extends LDefined[B]

  /** Claimed by an action coming from the left (i.e. from the corresponding [[LInvertSrc]]).
   *  Prevents the cell from being slated and removed by an action originating from the right.
   *  An action from the left has to eventually release the claim (even if the original action is obstructed).
   */
  case class LInvertTgtClaimed[A, B](src: Cell[A], inv: Inversion[B, A]) extends LDefined[B]

  case class LSkippingLeftLeft[A](newTgt: Cell[A], oldTgt: Cell[A]) extends LDefined[A]
  case class LSkippingLeftLRole[A, B](newTgt: Cell[A], newRole: RoleL[A, B], oldTgt: Cell[B]) extends LDefined[B]
  case class LSkippingLeftDown[A, B](invTgt: Cell[A], lInv: Inversion[A, B], oldTgt: Cell[B]) extends LDefined[B]
  case class LSkippingLeftUp[A, B](invSrc: Cell[A], lInv: Inversion[B, A], oldTgt: Cell[B]) extends LDefined[B]
  case class RSkippingDownLeft[A, B](rInv: Inversion[A, B], oldTgt: Cell[B], newTgt: Cell[B]) extends RDefined[A]
  case class RSkippingUpLeft  [A, B](newTgt: Cell[A], oldTgt: Cell[A], rInv: Inversion[A, B]) extends RDefined[B]
  case class LSkippingUpUp[A, B](newSrc: Cell[A], rInv: Inversion[A, B], oldSrc: Cell[B], lInv: Inversion[A, B]) extends LDefined[A]

  case class LRole[A, B](tgt: Cell[A], role: RoleL[A, B]) extends LDefined[B]
  case class RRole[A, B](role: RoleR[A, B], tgt: Cell[B]) extends RDefined[A]

  case object DoneSupplied extends LComplete[Done]
  case class DoneCallback(f: Either[Throwable, Unit] => Unit) extends RComplete[Done]

  case object NeedSupplied extends RComplete[Need]
  case class NeedCallback(f: Either[Throwable, Unit] => Unit) extends LComplete[Need]

  case object PingSupplied extends LComplete[Ping]
  case object PongSupplied extends RComplete[Pong]

  case class LStrengthenedPing(src: Cell[Ping]) extends LDefined[Done]

  case class LSplit[A1, A2](cell1: Cell[A1], cell2: Cell[A2]) extends LComplete[A1 |*| A2]
  case class RSplit[A1, A2](cell1: Cell[A1], cell2: Cell[A2]) extends RComplete[A1 |*| A2]

  case class LSplitInv[A, B](fst: Cell[-[A]], snd: Cell[-[B]]) extends LComplete[-[A |*| B]]
  case class RSplitInv[A, B](fst: Cell[-[A]], snd: Cell[-[B]]) extends RComplete[-[A |*| B]]
  case class LInvertSrcPair[A, B](tgt1: Cell[A], tgt2: Cell[B]) extends LComplete[-[A |*| B]]
  case class LInvertTgtPair[A, B](src1: Cell[-[A]], tgt2: Cell[-[B]]) extends LComplete[A |*| B]

  case class InjectedL[A, B](value: Cell[A]) extends LComplete[A |+| B]
  case class InjectedR[A, B](value: Cell[B]) extends LComplete[A |+| B]
  case class EitherSwitch[A, B, C](f: A -⚬ C, g: B -⚬ C, tgt: Cell[C]) extends RDefined[A |+| B]
  case class EitherWith[A, B, C](addendum: Cell[A], tgt: Cell[(A |*| B) |+| (A |*| C)]) extends RDefined[B |+| C]
  case class EitherCallback[A, B](f: Either[Throwable, Either[Cell[A], Cell[B]]] => Unit) extends RComplete[A |+| B]

  case class ChosenL[A, B](resultCell: Cell[A]) extends RComplete[A |&| B]
  case class ChosenR[A, B](resultCell: Cell[B]) extends RComplete[A |&| B]
  case class ChooseFrom[A, B, C](tgt: Cell[A], f: A -⚬ B, g: A -⚬ C) extends LDefined[B |&| C]
  case class ChoiceWith[A, B, C](tgt: Cell[(A |*| B) |&| (A |*| C)], addendum: Cell[A]) extends LDefined[B |&| C]

  case class JoinOf(src1: Cell[Done], src2: Cell[Done]) extends LDefined[Done]
  case class Join1(src1: Cell[Done]) extends LDefined[Done] // after Done from src2 has arrived
  case class Join2(src2: Cell[Done]) extends LDefined[Done] // after Done from src1 has arrived

  case class JoinNeedOf(src1: Cell[Need], src2: Cell[Need]) extends RDefined[Need]
  case class JoinNeed1(src1: Cell[Need]) extends RDefined[Need] // after Need from src2 has arrived
  case class JoinNeed2(src2: Cell[Need]) extends RDefined[Need] // after Need from src1 has arrived

  case class JoinPongOf(src1: Cell[Pong], src2: Cell[Pong]) extends RDefined[Pong]
  case class JoinPong1(src1: Cell[Pong]) extends RDefined[Pong] // after Pong from src2 has arrived
  case class JoinPong2(src2: Cell[Pong]) extends RDefined[Pong] // after Pong from src1 has arrived

  case class SelectOf(contestant1: Cell[Pong], contestant2: Cell[Pong]) extends RDefined[One |&| One]

  case class RNotifyEither[A, B](notificationCell: Cell[Ping], outCell: Cell[A |+| B]) extends RDefined[A |+| B]
  case class LNotifyChoice[A, B](notification: Cell[Pong], tgt: Cell[A |&| B]) extends LDefined[A |&| B]
  case class RNotifyDone(notification: Cell[Ping], tgt: Cell[Done]) extends RDefined[Done]
  case class LNotifyNeed(notification: Cell[Pong], tgt: Cell[Need]) extends LDefined[Need]

  case class InjectLOnPing[A, B](trigger: Cell[Ping], cellToInject: Cell[A]) extends LDefined[A |+| B]

  case class ValSupplied[A](value: A) extends LComplete[Val[A]]

  case class RMapValSrc[A, B](f: A => B, tgt: Cell[Val[B]]) extends RDefined[Val[A]]
  case class RConstVal[A](value: A, tgt: Cell[Val[A]]) extends RDefined[Done]
  case class LValTgt[A, B](src: Cell[A]) extends LDefined[Val[B]]

  case class RNeglectVal[A](tgt: Cell[Done]) extends RDefined[Val[A]]
  case class LDoneTgt[A](src: Cell[A]) extends LDefined[Done]

  case class RSplitVal[A, B](tgt1: Cell[Val[A]], tgt2: Cell[Val[B]]) extends RDefined[Val[(A, B)]]
  case class LZipVal[A, B](src1: Cell[Val[A]], src2: Cell[Val[B]]) extends LDefined[Val[(A, B)]]
  case class LZipVal1[A, B](src1: Cell[Val[A]], val2: B) extends LDefined[Val[(A, B)]]
  case class LZipVal2[A, B](val1: A, src2: Cell[Val[B]]) extends LDefined[Val[(A, B)]]

  case class RLiftEither[A, B](tgt: Cell[Val[A] |+| Val[B]]) extends RDefined[Val[Either[A, B]]]
  case class LLiftedEither[A, B](src: Cell[Val[Either[A, B]]]) extends LDefined[Val[A] |+| Val[B]]

  case class LCrashed[A](e: Throwable) extends LComplete[A]

  sealed trait ActionResult {
    import ActionResult._

    def takeUp(action: AbsorbableInstruction): FollowUpAction =
      this.startingAt(action.targetCell) match
        case thiz: FollowUpAction => thiz // already subsumes `action`
        case null                 => action and_? this

    protected def startingAt[X](cell: Cell[X]): FollowUpAction | Null =
      this match {
        case i: Instruction => if (cell eq i.targetCell) i else null
        case AllDone => null
        case Two(_1, _2) =>
          _1.startingAt(cell) match
            case a: FollowUpAction => Two(a, _2)
            case null => _2.startingAt(cell) match
              case b: FollowUpAction => Two(_1, b)
              case null => null
        case CallbackTriggered(f, x) => null
        case UnificationRequest(l, r) => null
        case ConnectionRequest(l, f, r) => null
      }
  }

  object ActionResult {
    case object AllDone extends ActionResult

    sealed trait FollowUpAction extends ActionResult {
      def and(that: FollowUpAction): FollowUpAction =
        Two(this, that)

      def and_?(that: ActionResult): FollowUpAction =
        that match
          case that: FollowUpAction => Two(this, that)
          case AllDone              => this

      final override def toString(): String =
        this match
          case Two(a, b) => s"Two($a, $b)"
          case UnificationRequest(l, r) => s"UnificationRequest(${addr(l)}, ${addr(r)})"
          case ConnectionRequest(l, f, r) => s"ConnectionRequest(${addr(l)}, $f, ${addr(r)})"
          case CallbackTriggered(f, x) => s"CallbackTriggered($f, $x)"
          case SupplyDone(t) => s"SupplyDone(${addr(t)})"
          case SupplyPing(t) => s"SupplyPing(${addr(t)})"
          case FillRoleR(s, r, t) => s"FillRoleR(${addr(s)}, $r, ${addr(t)})"
          case FillRoleL(t, r, s) => s"FillRoleL(${addr(t)}, $r, ${addr(s)})"
          case InjectL(l, r) => s"InjectL(${addr(l)}, ${addr(r)})"
          case InjectR(l, r) => s"InjectR(${addr(l)}, ${addr(r)})"
          case ChooseL(l, r) => s"ChooseL(${addr(l)}, ${addr(r)})"
          case ChooseR(l, r) => s"ChooseR(${addr(l)}, ${addr(r)})"
          case PropagateLCompletionRight(s, p, t) => s"PropagateLCompletionRight(${addr(s)}, $p, ${addr(t)})"
          case PropagateRCompletionLeft(t, p, s) => s"PropagateRCompletionLeft(${addr(t)}, $p, ${addr(s)})"
          case RefineLRole(l, r, t, p) => s"RefineLRole(${addr(l)}, $r, ${addr(t)}, $p)"
          case RefineRRole(cell, rRole, expectedRTarget, payload) => s"RefineRRole(${addr(cell)}, $rRole, ${addr(expectedRTarget)}, $payload)"
          case RefineLPart(expectedLCell, rRole, cell, payload) => s"RefineLPart(${addr(expectedLCell)}, $rRole, ${addr(cell)}, $payload)"
          case RefineRPart(cell, lRole, expectedRTarget, payload) => s"RefineRPart(${addr(cell)}, $lRole, ${addr(expectedRTarget)}, $payload)"
          case PropagateLCompletionUp(to, p, i, from) => s"PropagateLCompletionUp(${addr(to)}, $p, $i, ${addr(from)})"
          case RefineRInvertTgt(expectedInvSrc, rInv, invTgt, payload) => s"RefineRInvertTgt(${addr(expectedInvSrc)}, $rInv, ${addr(invTgt)}, $payload)"
          case PropagateRCompletionUp(to, p, i, from) => s"PropagateRCompletionUp(${addr(to)}, $p, $i, ${addr(from)})"
          case PropagateRCompletionDown(s, i, p, t) => s"PropagateRCompletionDown(${addr(s)}, $i, $p, ${addr(t)})"
          case RReciprocateForward(src, tgt) => s"RReciprocateForward(${addr(src)}, ${addr(tgt)})"
          case RReciprocateRInvert(src, inv, tgt) => s"RReciprocateRInvert(${addr(src)}, $inv, ${addr(tgt)})"
          case LReciprocateLInvert(src, inv, tgt) => s"LReciprocateLInvert(${addr(src)}, $inv, ${addr(tgt)})"
          case ContractBiFwd(l, slated, r) => s"ContractBiFwd(${addr(l)}, ${addr(slated)}, ${addr(r)})"
          case ContractLFwdRInvTgt(lCell, slated, rInv, src) => s"ContractLFwdRInvTgt(${addr(lCell)}, ${addr(slated)}, $rInv, ${addr(src)})"
          case ContractLFwdRInvSrc(lCell, slated, rInv, tgt) => s"ContractLFwdRInvSrc(${addr(lCell)}, ${addr(slated)}, $rInv, ${addr(tgt)})"
          case ContractLInvSrcRFwd(tgt, lInv, slated, rCell) => s"ContractLInvSrcRFwd(${addr(tgt)}, $lInv, ${addr(slated)}, ${addr(rCell)})"
          case ContractionLInvSrcRFwdClaimedTgt(contraction) => s"ContractionLInvSrcRFwdClaimedTgt($contraction)"
          case ContractLInvTgtRFwd(src, lInv, slated, rCell) => s"ContractLInvTgtRFwd(${addr(src)}, $lInv, ${addr(slated)}, ${addr(rCell)})"
          case ContractLInvSrcRInvTgt(src, rInv, slated, lInv, tgt) => s"ContractLInvSrcRInvTgt(${addr(src)}, $rInv, ${addr(slated)}, $lInv, ${addr(tgt)})"
          case SkipAhead(contraction) => s"SkipAhead($contraction)"
          case SkipToRInvSrc(contraction) => s"SkipToRInvSrc($contraction)"
          case SkipToRInvTgt(contraction) => s"SkipToRInvTgt($contraction)"
          case LSkipUpRight(contraction) => s"LSkipUpRight($contraction)"
          case LSkipDownRight(contraction) => s"LSkipDownRight($contraction)"
          case RSkipDownDown(contraction) => s"RSkipDownDown($contraction)"
          case ConsumeSlatedCell(l, slated, r) => s"ConsumeSlatedCell(${addr(l)}, ${addr(slated)}, ${addr(r)})"
          case CompleteBiFwdContraction(contraction) => s"CompleteBiFwdContraction($contraction)"
          case CompleteLFwdRInvTgtContraction(contraction) => s"CompleteLFwdRInvTgtContraction($contraction)"
          case CompleteLFwdRInvSrcContraction(contraction) => s"CompleteLFwdRInvSrcContraction($contraction)"
          case CompleteLInvSrcRFwdContraction(contraction) => s"CompleteLInvSrcRFwdContraction($contraction)"
          case CompleteLInvTgtRFwdContraction(contraction) => s"CompleteLInvTgtRFwdContraction($contraction)"
          case CompleteLInvSrcRInvTgtContraction(contraction) => s"CompleteLInvSrcRInvTgtContraction($contraction)"
          case LInvert(s, i, t) => s"LInvert(${addr(s)}, $i, ${addr(t)})"
          case LExpectDone(s, t) => s"LExpectDone(${addr(s)}, ${addr(t)})"
          case LExpectVal(s, t) => s"LExpectVal(${addr(s)}, ${addr(t)})"
          case LReciprocateLiftEither(s, t) => s"LReciprocateLiftEither(${addr(s)}, ${addr(t)})"
          case ConsumeAfterPropagationComplete(c) => s"ConsumeAfterPropagationComplete(${addr(c)})"
          case MapValTriggered(s, v, f, t) => s"MapValTriggered(${addr(s)}, $v, $f, ${addr(t)})"
    }

    case class Two(_1: FollowUpAction, _2: FollowUpAction) extends FollowUpAction

    case class UnificationRequest[X](l: Cell[X], r: Cell[X]) extends FollowUpAction
    case class ConnectionRequest[X, Y](l: Cell[X], f: X -⚬ Y, r: Cell[Y]) extends FollowUpAction

    case class CallbackTriggered[X](f: X => Unit, x: X) extends FollowUpAction

    case class MapValTriggered[X, Y](valueSrc: Cell[Val[X]], value: X, f: X => Y, tgt: Cell[Val[Y]]) extends FollowUpAction

    sealed trait Instruction extends FollowUpAction {
      type TargetCellType

      def targetCell: Cell[TargetCellType]
      def execute(): ActionResult
    }

    /** Instruction which may be skipped if another instruction starting at the same cell will be executed. */
    sealed trait AbsorbableInstruction extends Instruction // TODO: might need to distinguish l-absorbable and r-absorbable

    sealed trait CompleteContraction extends AbsorbableInstruction

    /** An action to refine `src` by pointing it at `receiver` to its right.
      *
      * @param src must be yet unconnected to the right
      * @param role the role `src` plays in `receiver`
      * @param receiver must already know that it will be fed from `src`
      */
    case class FillRoleR[A, B](src: Cell[A], role: RoleR[A, B], receiver: Cell[B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell: Cell[TargetCellType] = src

      override def execute(): ActionResult =
        src.modifyContentOptWith((src, RRole(role, receiver)), CellContent.fillRoleR)
    }

    /** An action to refine `src` by pointing it at `receiver` to its left.
      *
      * @param src must be yet unconnected to the left
      * @param role the role `src` plays in `receiver`
      * @param receiver must already know that it will be fed from `src`
      */
    case class FillRoleL[A, B](receiver: Cell[A], role: RoleL[A, B], src: Cell[B]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = src

      override def execute(): ActionResult =
        targetCell.modifyContentWith((LRole(receiver, role), src), CellContent.fillRoleL)
    }

    case class SupplyDone(cell: Cell[Done]) extends Instruction {
      override type TargetCellType = Done
      override def targetCell = cell

      override def execute(): ActionResult =
        targetCell.modifyContentWith(cell, CellContent.supplyDone)
    }

    case class SupplyPing(cell: Cell[Ping]) extends Instruction {
      override type TargetCellType = Ping
      override def targetCell = cell

      override def execute(): ActionResult =
        targetCell.modifyContentWith(cell, CellContent.supplyPing)
    }

    case class InjectL[A, B](lCell: Cell[A], rCell: Cell[A |+| B]) extends Instruction {
      override type TargetCellType = A |+| B
      override def targetCell = rCell

      override def execute(): ActionResult =
        targetCell.modifyContentWith(this, CellContent.injectL)
    }

    case class InjectR[A, B](lCell: Cell[B], rCell: Cell[A |+| B]) extends Instruction {
      override type TargetCellType = A |+| B
      override def targetCell = rCell

      override def execute(): ActionResult =
        targetCell.modifyContentWith(this, CellContent.injectR)
    }

    case class ChooseL[A, B](lCell: Cell[A |&| B], rCell: Cell[A]) extends Instruction {
      override type TargetCellType = A |&| B
      override def targetCell = lCell

      override def execute(): ActionResult =
        targetCell.modifyContentWith(this, CellContent.chooseL)
    }

    case class ChooseR[A, B](lCell: Cell[A |&| B], rCell: Cell[B]) extends Instruction {
      override type TargetCellType = A |&| B
      override def targetCell = lCell

      override def execute(): ActionResult =
        targetCell.modifyContentWith(this, CellContent.chooseR)
    }

    case class LInvert[A, B](invSrc: Cell[A], lInv: Inversion[B, A], invTgt: Cell[B]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = invTgt

      override def execute(): ActionResult =
        targetCell.modifyContentWith(this, CellContent.lInvertInit)
    }

    case class PropagateLCompletionRight[A, B](src: Cell[A], payload: LComplete[B], tgt: Cell[B]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = tgt

      override def execute(): ActionResult =
        targetCell.modifyContentWith(this, CellContent.propagateLCompletionRight)
    }

    case class RefineLRole[A, B](expectedLTarget: Cell[A], lRole: RoleL[A, B], cell: Cell[B], payload: LComplete[B]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = cell

      override def execute(): ActionResult =
        targetCell.modifyContentWith(this, CellContent.refineLRole)
    }

    case class PropagateRCompletionLeft[A](tgt: Cell[A], payload: RComplete[A], src: Cell[A]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = tgt

      override def execute(): ActionResult =
        targetCell.modifyContentWith(this, CellContent.propagateRCompletionLeft)
    }

    case class RefineRRole[A, B](cell: Cell[A], rRole: RoleR[A, B], expectedRTarget: Cell[B], payload: RComplete[A]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = cell

      override def execute(): ActionResult =
        targetCell.modifyContentWith(this, CellContent.refineRRole)
    }

    case class RefineLPart[A, B](expectedLCell: Cell[A], rRole: RoleR[A, B], cell: Cell[B], payload: LComplete[A]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = cell

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.refineLPart)
    }

    case class RefineRPart[A, B](cell: Cell[A], lRole: RoleL[A, B], expectedRTarget: Cell[B], payload: RComplete[B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = cell

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.refineRPart)
    }

    case class PropagateLCompletionUp[A, B](toInvSrc: Cell[A], payload: RComplete[A], rInv: Inversion[A, B], fromInvTgt: Cell[B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = toInvSrc

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.propagateLCompletionUp)
    }

    case class RefineRInvertTgt[A, B](expectedInvSrc: Cell[A], rInv: Inversion[A, B], invTgt: Cell[B], payload: RComplete[B]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = invTgt

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.refineRInvertTgt)
    }

    case class PropagateRCompletionUp[A, B](toInvSrc: Cell[A], payload: LComplete[A], lInv: Inversion[B, A], fromInvTgt: Cell[B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = toInvSrc

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.propagateRCompletionUp)
    }

    case class PropagateRCompletionDown[A, B](invSrc: Cell[A], lInv: Inversion[B, A], payload: LComplete[B], invTgt: Cell[B]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = invTgt

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.propagateRCompletionDown)
    }

    case class RReciprocateForward[A](src: Cell[A], tgt: Cell[A]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = src

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith((src, tgt), CellContent.rReciprocateFwd)
    }

    case class RReciprocateRInvert[A, B](src: Cell[A], inv: Inversion[A, B], tgt: Cell[B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = src

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.rReciprocateRInvert)
    }

    case class LReciprocateLInvert[A, B](src: Cell[A], inv: Inversion[B, A], tgt: Cell[B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = src

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.lReciprocateLInvert)
    }

    case class ContractBiFwd[A](l: Cell[A], slated: Cell[A], r: Cell[A]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = r

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.initBiFwdContraction)
    }

    case class ContractLFwdRInvTgt[A, B](lCell: Cell[A], slated: Cell[A], rInv: Inversion[B, A], src: Cell[B]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = src

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.initLFwdRInvTgtContraction)
    }

    case class ContractLFwdRInvSrc[A, B](lCell: Cell[A], slated: Cell[A], rInv: Inversion[A, B], tgt: Cell[B]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = tgt

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.initLFwdRInvSrcContraction)
    }

    case class ContractLInvSrcRFwd[A, B](tgt: Cell[A], lInv: Inversion[A, B], slated: Cell[B], rCell: Cell[B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = tgt

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.initContractionLInvSrcRFwdClaimTgt)
    }

    case class ContractionLInvSrcRFwdClaimedTgt[A, B](contraction: ContractLInvSrcRFwd[A, B]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = contraction.rCell

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.initContractionLInvSrcRFwdAfterTgtClaimed)
    }

    case class ContractLInvTgtRFwd[A, B](src: Cell[A], lInv: Inversion[B, A], slated: Cell[B], rCell: Cell[B]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = rCell

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.initContractionLInvTgtRFwd)
    }

    case class ContractLInvSrcRInvTgt[A, B](src: Cell[A], rInv: Inversion[A, B], slated: Cell[B], lInv: Inversion[A, B], tgt: Cell[A]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = tgt

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.initContractionLInvSrcRInvTgt)
    }

    object ContractLInvSrcRInvTgt {
      def mk[A, B, C](src: Cell[A], rInv: Inversion[A, B], slated: Cell[B], lInv: Inversion[C, B], tgt: Cell[C]): ContractLInvSrcRInvTgt[A, B] = {
        val `A=C` = rInv.alsoFrom[C](lInv)
        val lInv1: Inversion[A, B] = `A=C`.substituteContra[[x] =>> Inversion[x, B]](lInv)
        val tgt1: Cell[A]          = `A=C`.substituteContra[Cell](tgt)
        ContractLInvSrcRInvTgt[A, B](src, rInv, slated, lInv1, tgt1)
      }
    }

    case class SkipAhead[A](contraction: ContractBiFwd[A]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = contraction.l

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.skipAhead)
    }

    case class SkipToRInvSrc[A, B](contraction: ContractLFwdRInvTgt[A, B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = contraction.lCell

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.skipToRInvSrc)
    }

    case class SkipToRInvTgt[A, B](contraction: ContractLFwdRInvSrc[A, B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = contraction.lCell

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.skipToRInvTgt)
    }

    case class LSkipUpRight[A, B](contraction: ContractLInvSrcRFwd[A, B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = contraction.tgt

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.lSkipUpRight)
    }

    case class LSkipDownRight[A, B](contraction: ContractLInvTgtRFwd[A, B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = contraction.src

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.lSkipDownRight)
    }

    case class RSkipDownDown[A, B](contraction: ContractLInvSrcRInvTgt[A, B]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = contraction.src

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.rSkipDownDown)
    }

    case class CompleteBiFwdContraction[A](contraction: ContractBiFwd[A]) extends CompleteContraction {
      override type TargetCellType = A
      override def targetCell = contraction.r

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.completeBiFwdContraction)
    }

    case class CompleteLFwdRInvTgtContraction[A, B](contraction: ContractLFwdRInvTgt[A, B]) extends CompleteContraction {
      override type TargetCellType = B
      override def targetCell = contraction.src

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.completeLFwdRInvTgtContraction)
    }

    case class CompleteLFwdRInvSrcContraction[A, B](contraction: ContractLFwdRInvSrc[A, B]) extends CompleteContraction {
      override type TargetCellType = B
      override def targetCell = contraction.tgt

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.completeLFwdRInvSrcContraction)
    }

    case class CompleteLInvSrcRFwdContraction[A, B](contraction: ContractLInvSrcRFwd[A, B]) extends CompleteContraction {
      override type TargetCellType = B
      override def targetCell = contraction.rCell

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.completeLInvSrcRFwdContraction)
    }

    case class CompleteLInvTgtRFwdContraction[A, B](contraction: ContractLInvTgtRFwd[A, B]) extends CompleteContraction {
      override type TargetCellType = B
      override def targetCell = contraction.rCell

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.completeLInvTgtRFwdContraction)
    }

    case class CompleteLInvSrcRInvTgtContraction[A, B](contraction: ContractLInvSrcRInvTgt[A, B]) extends CompleteContraction {
      override type TargetCellType = A
      override def targetCell = contraction.tgt

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(contraction, CellContent.completeLInvSrcRInvTgtContraction)
    }

    case class ConsumeSlatedCell[A, B, C](l: Cell[A], slated: Cell[B], r: Cell[C]) extends Instruction {
      override type TargetCellType = B
      override def targetCell = slated

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.consumeSlatedCell)
    }

    case class ConsumeAfterPropagationComplete[A](cell: Cell[A]) extends Instruction {
      override type TargetCellType = A
      override def targetCell = cell
      override def execute(): ActionResult =
        targetCell.modifyContentOpt(CellContent.consumeAfterPropagationComplete)
    }

    case class LExpectVal[A, B](src: Cell[A], tgt: Cell[Val[B]]) extends AbsorbableInstruction {
      override type TargetCellType = Val[B]
      override def targetCell = tgt

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.lExpectVal)
    }

    case class LExpectDone[A](src: Cell[A], tgt: Cell[Done]) extends AbsorbableInstruction {
      override type TargetCellType = Done
      override def targetCell = tgt

      override def execute(): ActionResult =
        targetCell.modifyContentWith(this, CellContent.lExpectDone)
    }

    case class LReciprocateLiftEither[A, B](src: Cell[Val[Either[A, B]]], tgt: Cell[Val[A] |+| Val[B]]) extends Instruction {
      override type TargetCellType = Val[A] |+| Val[B]
      override def targetCell = tgt

      override def execute(): ActionResult =
        targetCell.modifyContentOptWith(this, CellContent.lReciprocateLiftEither)
    }
  }
  import ActionResult._

  val supplyDone: (CellContent[Done], Cell[Done]) => (CellContent[Done], ActionResult) = {
    (content, self) =>
      content match
        case Empty()          => (DoneSupplied, AllDone)
        case RFwd(tgt)        => (Consumed(), PropagateLCompletionRight(self, DoneSupplied, tgt))
        case RInvertSrc(i, t) => (Consumed(), RefineRInvertTgt(self, i, t, DoneSupplied.rInvert(i)))
        case RConstVal(a, t)  => (Consumed(), PropagateLCompletionRight(self, ValSupplied(a), t))
        case RNotifyDone(n, t) =>
          val followUp =
            RefineLRole(self, RoleL.DoneNotification, n, PingSupplied) and
            RefineLRole(self, RoleL.NotifyDoneTgt, t, DoneSupplied)
          (Consumed(), followUp)
        case r: RSkippingDownLeft[Done, y] => (BiDef(DoneSupplied, r), AllDone)
        case DoneSupplied =>
          throw new IllegalStateException("Double completion")
  }

  val supplyPing: (CellContent[Ping], Cell[Ping]) => (CellContent[Ping], ActionResult) = {
    (content, self) =>
      content match
        case Empty()            => (PingSupplied, AllDone)
        case RFwd(tgt)          => (Consumed(), PropagateLCompletionRight(self, PingSupplied, tgt))
        case RRole(role, tgt)   => (Consumed(), RefineLPart(self, role, tgt, PingSupplied))
        case RInvertSrc(i, tgt) => (Consumed(), RefineRInvertTgt(expectedInvSrc = self, i, tgt, PingSupplied.rInvert(i)))
        case PingSupplied       => throw new IllegalStateException("Double completion")
  }

  val supplyPong: (CellContent[Pong], Cell[Pong]) => (CellContent[Pong], ActionResult) = {
    (content, self) =>
      content match
        case Empty()                    => (PongSupplied, AllDone)
        case l @ LFwd(tgt)              => (PropagatingRCompletion(l, PongSupplied), PropagateRCompletionLeft(tgt, PongSupplied, self))
        case l: LSkippingLeftLeft[Pong] => (BiDef(l, PongSupplied), AllDone)
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
        case r @ RFwd(tgt) =>
          val a = Cell.empty[A]
          val b = Cell.empty[B]
          val l = LSplit(a, b)
          (Consumed(), (a, b, PropagateLCompletionRight(self, l, tgt)))
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
        case l: LDefined[A |*| B] =>
          val a = Cell.empty[A]
          val b = Cell.empty[B]
          val payload = RSplit(a, b)
          val (content, res) = combineLDefinedRSplit(self, l, payload)
          (content, (a, b, res))
        case _: RDefined[A |*| B] | Consumed() =>
          throw new IllegalStateException("The cell is already right-connected")
  }

  def consumeAfterPropagationComplete[A]: CellContent[A] => (Option[CellContent[A]], ActionResult) = {
    case PropagatingRCompletion(l, r) => (Some(Consumed()), AllDone)
    case PropagatingLCompletion(l, r) => (Some(Consumed()), AllDone)
    case Consumed()                   => (None, AllDone)
  }

  def injectL[A, B]: (CellContent[A |+| B], InjectL[A, B]) => (CellContent[A |+| B], ActionResult) = {
    (tgt, inj) =>
      val InjectL(src, self) = inj
      tgt match {
        case Empty() =>
          (InjectedL(src), AllDone)
        case EitherCallback(f) =>
          (Consumed(), CallbackTriggered(f, Right(Left(src))))
        case EitherSwitch(f, g, tgt) =>
          (Consumed(), ConnectionRequest(src, f, tgt))
        case RFwd(rTgt) =>
          (Consumed(), PropagateLCompletionRight(self, InjectedL(src), rTgt))
        case RInvertSrc(i, tgt) =>
          (Consumed(), RefineRInvertTgt(self, i, tgt, InjectedL(src).rInvert(i)))
        case _: LDefined[A |+| B] | Consumed() =>
          throw new IllegalStateException(s"The target cell is already left-connected: $tgt")
      }
  }

  def injectR[A, B]: (CellContent[A |+| B], InjectR[A, B]) => (CellContent[A |+| B], ActionResult) = {
    (tgtContent, inj) =>
      val InjectR(srcCell, self) = inj
      tgtContent match {
        case Empty() =>
          (InjectedR(srcCell), AllDone)
        case EitherCallback(f) =>
          (Consumed(), CallbackTriggered(f, Right(Right(srcCell))))
        case EitherSwitch(f, g, tgtCell) =>
          (Consumed(), ConnectionRequest(srcCell, g, tgtCell))
        case RFwd(tgt1) =>
          (Consumed(), PropagateLCompletionRight(self, InjectedR(srcCell), tgt1))
        case RInvertSrc(i, tgt) =>
          (Consumed(), RefineRInvertTgt(self, i, tgt, InjectedR(srcCell).rInvert(i)))
        case _: LDefined[A |+| B] | Consumed() =>
          throw new IllegalStateException("The target cell is already left-connected")
      }
  }

  def eitherSwitch[A, B, C]: (CellContent[A |+| B], EitherSwitch[A, B, C]) => (CellContent[A |+| B], ActionResult) = {
    (eitherContent, payload) =>
      eitherContent match {
        case Empty()                => (payload, AllDone)
        case l: InjectLOnPing[A, B] => (BiDef(l, payload), AllDone)
        case l: LLiftedEither[A, B] => (BiDef(l, payload), AllDone)
      }
  }

  def chooseL[A, B]: (CellContent[A |&| B], ChooseL[A, B]) => (CellContent[A |&| B], ActionResult) = {
    (choiceContent, cells) =>
      val ChooseL(self, resultCell) = cells
      choiceContent match {
        case Empty() =>
          (ChosenL(resultCell), AllDone)
        case ChooseFrom(lTgt, f, _) =>
          (Consumed(), ConnectionRequest(lTgt, f, resultCell))
        case l @ LFwd(tgt) =>
          val payload = ChosenL[A, B](resultCell)
          (PropagatingRCompletion(l, payload), PropagateRCompletionLeft(tgt, payload, self))
        case l: LSkippingLeftLeft[A |&| B] =>
          (BiDef(l, ChosenL(resultCell)), AllDone)
        case LNotifyChoice(notification, tgt) =>
          val followUp =
            RefineRRole(notification, RoleR.ChoiceNotification(), self, PongSupplied) and
            RefineRRole(tgt, RoleR.NotifyChoiceTgt(), self, ChosenL(resultCell))
          (Consumed(), followUp)
      }
  }

  def chooseR[A, B]: (CellContent[A |&| B], ChooseR[A, B]) => (CellContent[A |&| B], ActionResult) = {
    (choiceContent, cells) =>
      val ChooseR(self, resultCell) = cells
      choiceContent match {
        case Empty() =>
          (ChosenR(resultCell), AllDone)
        case ChooseFrom(lTgt, _, g) =>
          (Consumed(), ConnectionRequest(lTgt, g, resultCell))
        case l @ LFwd(tgt) =>
          val payload = ChosenR[A, B](resultCell)
          (PropagatingRCompletion(l, payload), PropagateRCompletionLeft(tgt, payload, self))
        case l: LInvertTgt[x, A |&| B] =>
          // wait for inversions to cancel out
          (BiDef(l, ChosenR(resultCell)), AllDone)
        case l: LInvertTgtClaimed[x, A |&| B] =>
          (BiDef(l, ChosenR(resultCell)), AllDone)
        case l: LSkippingLeftLeft[A |&| B] =>
          (BiDef(l, ChosenR(resultCell)), AllDone)
        case l: LNotifyChoice[A, B] =>
          val followUp =
            RefineRRole(l.notification, RoleR.ChoiceNotification(), expectedRTarget = self, PongSupplied) and
            RefineRRole(l.tgt, RoleR.NotifyChoiceTgt(), expectedRTarget = self, ChosenR(resultCell))
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
        case r: RRole[B |&| C, d] => (BiDef(ch, r), AllDone)
        case r: RSkippingDownLeft[B |&| C, y] => (BiDef(ch, r), AllDone)
      }
  }

  def eitherWith[A, B, C]: (CellContent[B |+| C], EitherWith[A, B, C]) => (CellContent[B |+| C], ActionResult) = {
    (srcContent, payload) =>
      srcContent match {
        case l: LDefined[B |+| C] => (BiDef(l, payload), AllDone)
        case Empty()              => (payload, AllDone)
      }
  }

  def choiceWith[A, B, C]: (CellContent[B |&| C], ChoiceWith[A, B, C]) => (CellContent[B |&| C], ActionResult) = {
    (src, ch) =>
      src match {
        case Empty()        => (ch, AllDone)
        case rFwd @ RFwd(_) => (BiDef(ch, rFwd), AllDone)
        case ChosenR(rTgt)  => (Consumed(), ChooseR(ch.tgt, Cell(RSplit(ch.addendum, rTgt))))
        case ChosenL(rTgt)  => (Consumed(), ChooseL(ch.tgt, Cell(RSplit(ch.addendum, rTgt))))
      }
  }

  val makeAJoinOf: (CellContent[Done], (Cell[Done], JoinOf)) => (CellContent[Done], ActionResult) = {
    (content, cellAndJoiners) =>
      import RoleR.{Joiner1, Joiner2}

      val (self, joiners) = cellAndJoiners
      content match {
        case Empty() =>
          val followUp =
            FillRoleR(joiners.src1, Joiner1, self) and
            FillRoleR(joiners.src2, Joiner2, self)
          (joiners, followUp)
        case r: RDefined[Done] =>
          val followUp =
            FillRoleR(joiners.src1, Joiner1, self) and
            FillRoleR(joiners.src2, Joiner2, self)
          (BiDef(joiners, r), followUp)
      }
  }

  val makeAJoinNeedOf: (CellContent[Need], (Cell[Need], JoinNeedOf)) => (CellContent[Need], ActionResult) = {
    import RoleL.{JoinerNeed1, JoinerNeed2}

    (tgtContent, cellAndJoiners) =>
      val (self, joiners) = cellAndJoiners

      def followUp =
        FillRoleL(self, JoinerNeed1, joiners.src1) and
        FillRoleL(self, JoinerNeed2, joiners.src2)

      tgtContent match {
        case Empty() =>
          (joiners, followUp)
      }
  }

  val makeAJoinPongOf: (CellContent[Pong], (Cell[Pong], JoinPongOf)) => (CellContent[Pong], ActionResult) = {
    (content, cellAndJoiners) =>
      import RoleL.{JoinerPong1, JoinerPong2}

      val (self, joiners) = cellAndJoiners
      content match {
        case Empty() =>
          val followUp =
            FillRoleL(self, JoinerPong1, joiners.src1) and
            FillRoleL(self, JoinerPong2, joiners.src2)
          (joiners, followUp)
        case l: LDefined[Pong] =>
          val followUp =
            FillRoleL(self, JoinerPong1, joiners.src1) and
            FillRoleL(self, JoinerPong2, joiners.src2)
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
            FillRoleL(self, SelectContestant1, contestants.contestant1) and
            FillRoleL(self, SelectContestant2, contestants.contestant2)
          (contestants, followUp)
        case l @ LFwd(_) =>
          val followUp =
            FillRoleL(self, SelectContestant1, contestants.contestant1) and
            FillRoleL(self, SelectContestant2, contestants.contestant2)
          (BiDef(l, contestants), followUp)
      }
  }

  def notifyEither[A, B]: (CellContent[A |+| B], (Cell[A |+| B], RNotifyEither[A, B])) => (CellContent[A |+| B], ActionResult) = {
    (srcContent, cellAndPayload) =>
      import RoleL.{EitherNotification, NotifyEitherTgt}

      val (self, payload) = cellAndPayload

      def followUp =
        FillRoleL(self, EitherNotification(), payload.notificationCell) and
        FillRoleL(self, NotifyEitherTgt(), payload.outCell)

      srcContent match {
        case Empty() =>
          (payload, followUp)
        case InjectedL(lCell) =>
          val followUp =
            SupplyPing(payload.notificationCell) and
            InjectL(lCell, payload.outCell)
          (Consumed(), followUp)
        case l: LFwd[A |+| B] =>
          (BiDef(l, payload), followUp)
        case l: LSkippingLeftLeft[A |+| B] =>
          (BiDef(l, payload), followUp)
      }
  }

  val notifyDone: (CellContent[Done], (Cell[Done], RNotifyDone)) => (CellContent[Done], ActionResult) = {
    import RoleL.{DoneNotification, NotifyDoneTgt}

    (srcContent, cellAndPayload) =>
      val (self, payload) = cellAndPayload

      def followUp =
        FillRoleL(self, DoneNotification, payload.notification) and
        FillRoleL(self, NotifyDoneTgt, payload.tgt)

      srcContent match {
        case Empty() =>
          (payload, followUp)
        case DoneSupplied =>
          val followUp =
            SupplyPing(payload.notification) and
            SupplyDone(payload.tgt)
          (Consumed(), followUp)
        case l: LFwd[Done] =>
          (BiDef(l, payload), followUp)
      }
  }

  val notifyNeed: (CellContent[Need], (LNotifyNeed, Cell[Need])) => (CellContent[Need], ActionResult) = {
    (srcContent, payloadAndCell) =>
      import RoleR.{NeedNotification, NotifyNeedTgt}

      val (payload, self) = payloadAndCell

      def followUp =
        FillRoleR(payload.notification, NeedNotification, self) and
        FillRoleR(payload.tgt, NotifyNeedTgt, self)

      srcContent match {
        case Empty() =>
          (payload, followUp)
        case r: RFwd[Need] =>
          (BiDef(payload, r), followUp)
        case r: RInvertTgt[x, Need] =>
          (BiDef(payload, r), followUp)
        case r: RSkippingUpLeft[x, Need] =>
          (BiDef(payload, r), followUp)
        case NeedSupplied =>
          val followUp =
            RefineRRole(payload.notification, NeedNotification, self, PongSupplied) and
            RefineRRole(payload.tgt, NotifyNeedTgt, self, NeedSupplied)
          (Consumed(), followUp)
        case r: (JoinNeedOf | JoinNeed1 | JoinNeed2) =>
          (BiDef(payload, r), followUp)
      }
  }

  def notifyChoice[A, B]: (CellContent[A |&| B], (LNotifyChoice[A, B], Cell[A |&| B])) => (CellContent[A |&| B], ActionResult) = {
    (srcContent, payloadAndCell) =>
      import RoleR.{ChoiceNotification, NotifyChoiceTgt}

      val (payload, self) = payloadAndCell

      def nextStep =
        FillRoleR(payload.notification, ChoiceNotification(), self) and
        FillRoleR(payload.tgt, NotifyChoiceTgt(), self)

      srcContent match {
        case Empty() =>
          (payload, nextStep)
        case cl @ ChosenL(_) =>
          val followUp =
            RefineRRole(payload.notification, ChoiceNotification(), self, PongSupplied) and
            RefineRRole(payload.tgt, NotifyChoiceTgt(), self, cl)
          (Consumed(), followUp)
        case cr @ ChosenR(_) =>
          val followUp =
            RefineRRole(payload.notification, ChoiceNotification(), self, PongSupplied) and
            RefineRRole(payload.tgt, NotifyChoiceTgt(), self, cr)
          (Consumed(), followUp)
        case r: RFwd[A |&| B] =>
          (BiDef(payload, r), nextStep)
        case r: RInvertSrc[A |&| B, y] =>
          (BiDef(payload, r), nextStep)
      }
  }

  def injectLOnPing[A, B]: (CellContent[A |+| B], (Cell[Ping], Cell[A], Cell[A |+| B])) => (CellContent[A |+| B], ActionResult) = {
    (tgtContent, cells) =>
      import RoleR.InjectionTrigger

      val (pingCell, injectedCell, self) = cells

      def newContentL = InjectLOnPing[A, B](pingCell, injectedCell)
      def followUp    = FillRoleR(pingCell, InjectionTrigger(), self)

      tgtContent match {
        case Empty() =>
          (newContentL, followUp)
        case r: RDefined[A |+| B] =>
          (BiDef(newContentL, r), followUp)
      }
  }

  def fillRoleR[A, B]: (CellContent[A], (Cell[A], RRole[A, B])) => (Option[CellContent[A]], ActionResult) = {
    (src, cellAndLink) =>
      val (self, rRole) = cellAndLink
      src match {
        case l: LDefined[A] =>
          val (newContent, res) = combine(self, l, rRole)
          (Some(newContent), res)
        case Empty() =>
          (Some(rRole), AllDone)
        case r: RComplete[A] =>
          (None, AllDone)
        case PropagatingRCompletion(_, _) | Consumed() =>
          (None, AllDone)
      }
  }

  def fillRoleL[A, B]: (CellContent[B], (LRole[A, B], Cell[B])) => (CellContent[B], ActionResult) = {
    (src, lRoleSelf) =>
      val (lRole, self) = lRoleSelf
      src match {
        case r: RDefined[B] =>
          val (newContent, res) = combine(self, lRole, r)
          (newContent, res)
        case Empty()=>
          (lRole, AllDone)
      }
  }

  def unifyInit[A]: (CellContent[A], (Cell[A], Cell[A])) => (CellContent[A], ActionResult) = {
    (rContent, cells) =>
      val (lCell, self) = cells
      rContent match {
        case Empty()                  => (LFwd(lCell), RReciprocateForward(lCell, self))
        case r: RComplete[A]          => (PropagatingRCompletion(LFwd(lCell), r), PropagateRCompletionLeft(lCell, r, self))
        case r: RFwd[A]               => (Slated(LFwd(lCell), r), ContractBiFwd(lCell, self, r.tgt))
        case r @ RRole(role, tgt)     => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r @ RInvertSrc(i, tgt)   => (Slated(LFwd(lCell), r), ContractLFwdRInvSrc(lCell, self, i, tgt)) // TODO: also create reciprocal link in case the contraction is obstructed
        case r: SelectOf              => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r: JoinNeedOf            => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r: JoinPongOf            => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r @ RInvertTgt(src, i)   => (Slated(LFwd(lCell), r), ContractLFwdRInvTgt(lCell, self, i, src)) // TODO: also create reciprocal link in case the contraction is obstructed
        case r: RSkippingUpLeft[x, A] => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r: RSkippingDownLeft[A, y] => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r: RNotifyDone           => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r: RNotifyEither[x, y]   => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r: RMapValSrc[x, y]      => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r: RConstVal[x]          => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r: EitherSwitch[x, y, z] => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case r: EitherWith[x, y, z]   => (BiDef(LFwd(lCell), r), RReciprocateForward(lCell, self))
        case _: LDefined[A] | Slated(_, _) | BiDef(_, _) | PropagatingLCompletion(_, _) | PropagatingRCompletion(_, _) | Consumed() =>
          throw IllegalStateException(s"Cell ${addr(self)} is already connected to the left: $rContent")
      }
  }

  def rReciprocateFwd[A]: (CellContent[A], (Cell[A], Cell[A])) => (Option[CellContent[A]], ActionResult) = {
    (lContent, cells) =>
      val (self, rCell) = cells
      lContent match {
        case Empty()                => (Some(RFwd(rCell)), AllDone)
        case DoneSupplied           => (Some(Consumed()), PropagateLCompletionRight(self, DoneSupplied, rCell))
        case PingSupplied           => (Some(Consumed()), PropagateLCompletionRight(self, PingSupplied, rCell))
        case l: NeedCallback        => (Some(Consumed()), PropagateLCompletionRight(self, l, rCell))
        case l: InjectedR[x, y]     => (Some(Consumed()), PropagateLCompletionRight(self, l, rCell))
        case l: LSplit[x, y]        => (Some(Consumed()), PropagateLCompletionRight(self, l, rCell))
        case l: ValSupplied[a]      => (Some(Consumed()), PropagateLCompletionRight(self, l, rCell))
        case l: LCompleteInv[x]     => (Some(Consumed()), PropagateLCompletionRight(self, l, rCell))
        case l: LFwd[x]             => (Some(Slated(l, RFwd(rCell))), ContractBiFwd(l.tgt, slated = self, rCell))
        case l: LInvertSrc[A, x]    => (Some(Slated(l, RFwd(rCell))), ContractLInvSrcRFwd(l.tgt, l.inv, slated = self, rCell))
        case l: LInvertTgt[x, A]    => (Some(Slated(l, RFwd(rCell))), ContractLInvTgtRFwd(l.src, l.inv, slated = self, rCell))
        case l: LRole[x, y]         => (Some(BiDef(l, RFwd(rCell))), AllDone)
        case l: LSkippingLeftLeft[x]      => (Some(BiDef(l, RFwd(rCell))), AllDone)
        case l: LSkippingLeftLRole[x, y]  => (Some(BiDef(l, RFwd(rCell))), AllDone)
        case l: LSkippingLeftUp[x, A]     => (Some(BiDef(l, RFwd(rCell))), AllDone)
        case l: LSkippingLeftDown[x, A]   => (Some(BiDef(l, RFwd(rCell))), AllDone)
        case l: LSkippingUpUp[A, x]       => (Some(BiDef(l, RFwd(rCell))), AllDone)
        case j: JoinOf                    => (Some(BiDef(j, RFwd(rCell))), AllDone)
        case c: ChooseFrom[x, y, z]       => (Some(BiDef(c, RFwd(rCell))), AllDone)
        case c: ChoiceWith[x, y, z]       => (Some(BiDef(c, RFwd(rCell))), AllDone)
        case l: LNotifyNeed               => (Some(BiDef(l, RFwd(rCell))), AllDone)
        case l: LInvertTgtClaimed[x, A]   => (Some(BiDef(l, RFwd(rCell))), AllDone)
        case l: LStrengthenedPing         => (Some(BiDef(l, RFwd(rCell))), AllDone)
        case l: LValTgt[x, a]             => (Some(BiDef(l, RFwd(rCell))), AllDone)

        // overtaken
        case PropagatingRCompletion(_, _) => (None, AllDone)
        case BiDef(_, _)      => (None, AllDone)
        case RSplit(_, _)     => (None, AllDone)
        case ChosenR(_)       => (None, AllDone)
        case ChosenL(_)       => (None, AllDone)
        case Consumed()       => (None, AllDone)
        case RInvertSrc(_, _) => (None, AllDone)
        case RInvertTgt(_, _) => (None, AllDone)
        case RFwd(_)          => (None, AllDone)
        case Slated(_, _)     => (None, AllDone)
        case DoneCallback(_)  => (None, AllDone)
        case PongSupplied     => (None, AllDone)
      }
  }

  val strengthenPing: (CellContent[Done], (Cell[Ping], Cell[Done])) => (CellContent[Done], ActionResult) = {
    (tgtContent, cells) =>
      val (src, self) = cells

      def newContentL = LStrengthenedPing(src)
      def followUp    = FillRoleR(src, RoleR.StrengthenPingSrc, self)

      tgtContent match {
        case Empty() =>
          (newContentL, followUp)
        case r: RDefined[Done] =>
          val (content, action) = combine(self, newContentL, r)
          (content, followUp and_? action)
      }
  }

  def lsplitInv[A, B]: (CellContent[-[A |*| B]], (LSplitInv[A, B], Cell[-[A |*| B]])) => (CellContent[-[A |*| B]], ActionResult) = {
    (rContent, payloadAndCell) =>
      val (payload, self) = payloadAndCell

      rContent match {
        case RSplitInv(a, b) =>
          (Consumed(), UnificationRequest(payload.fst, a) and UnificationRequest(payload.snd, b))
        case Empty() =>
          (payload, AllDone)
      }
  }

  def rsplitInv[A, B]: (CellContent[-[A |*| B]], (Cell[-[A |*| B]], RSplitInv[A, B])) => (CellContent[-[A |*| B]], ActionResult) = {
    (lContent, cellAndPayload) =>
      val (self, payload) = cellAndPayload
      lContent match {
        case l @ LFwd(lTgt) =>
          (PropagatingRCompletion(l, payload), PropagateRCompletionLeft(lTgt, payload, self))
        case l: LSkippingLeftLeft[-[A |*| B]] =>
          (BiDef(l, payload), AllDone)
        case LSplitInv(a, b) =>
          (Consumed(), UnificationRequest(a, payload.fst) and UnificationRequest(b, payload.snd))
        case l: LInvertSrcPair[A, B] =>
          val followUp =
            LInvert(payload.fst, Inversion.Universal(), l.tgt1) and
            LInvert(payload.snd, Inversion.Universal(), l.tgt2)
          (Consumed(), followUp)
        case LCompleteInv(r0) =>
          r0 match
            case RSplit(cell1, cell2) =>
              val followUp =
                LInvert(payload.fst, Inversion.Universal(), cell1) and
                LInvert(payload.snd, Inversion.Universal(), cell2)
              (Consumed(), followUp)
        case Empty() =>
          (payload, AllDone)
      }
  }

  def rInvertInit[A, B]: (CellContent[B], (Cell[A], Inversion[A, B], Cell[B])) => (CellContent[B], ActionResult) = {
    (tgtContent, srcInvTgt) =>
      val (src, inv, self) = srcInvTgt

      def newContentR = RInvertTgt(src, inv)
      def nextStep    = RReciprocateRInvert(src, inv, self)

      tgtContent match {
        case Empty()                    => (newContentR, nextStep)
        case l: LFwd[B]                 => (Slated(l, newContentR), ContractLFwdRInvTgt(l.tgt, self, inv, src))
        case l @ LInvertSrc(i, tgt)     => (Slated(l, newContentR), nextStep and ContractLInvSrcRInvTgt.mk(src, inv, self, i, tgt))
        case l: LInvertTgt[x, B]        => (BiDef(l, newContentR), nextStep)
        case l: LSkippingLeftLeft[B]    => (BiDef(l, newContentR), nextStep)
        case l: LSkippingLeftDown[x, B] => (BiDef(l, newContentR), nextStep)
        case l: LSkippingLeftUp[x, B]   => (BiDef(l, newContentR), nextStep)
        case l: LInvertTgtClaimed[x, B] => (BiDef(l, newContentR), nextStep)
        case l: LComplete[B]            => (PropagatingLCompletion(l, newContentR), PropagateLCompletionUp(src, l.rUnInvert(inv), inv, self))
      }
  }

  def lInvertInit[A, B]: (CellContent[B], LInvert[A, B]) => (CellContent[B], ActionResult) = {
    (tgtContent, inversion) =>
      val LInvert(src, inv, self) = inversion

      def newContentL = LInvertTgt(src, inv)
      def nextStep    = LReciprocateLInvert(src, inv, self)

      tgtContent match {
        case Empty() =>
          (newContentL, nextStep)
        case r: RFwd[B] =>
          (Slated(newContentL, r), nextStep and ContractLInvTgtRFwd(src, inv, self, r.tgt))
        case r: RInvertSrc[B, y] =>
          // not contracting in the current version
          // TODO: Do contract. Use Iso[A, y].
          (BiDef(newContentL, r), nextStep)
        case r: RInvertTgt[x, B] =>
          (BiDef(newContentL, r), nextStep)
        case r: RSkippingUpLeft[x, B] =>
          (BiDef(newContentL, r), nextStep)
        case r: RComplete[B] =>
          (PropagatingRCompletion(newContentL, r), PropagateRCompletionUp(src, r.lInvert(inv), inv, self))
        case r: RNeglectVal[b] =>
          // TODO: propagate the neglecting towards the source
          (BiDef(newContentL, r), nextStep)
        case r: RRole[B, y] =>
          (BiDef(newContentL, r), nextStep)
      }
  }

  def rReciprocateRInvert[A, B]: (CellContent[A], RReciprocateRInvert[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (invSrcContent, inversion) =>
      val RReciprocateRInvert(self, inv, invTgt) = inversion
      def newContentR = RInvertSrc(inv, invTgt)

      invSrcContent match {
        case l: LDefined[A] =>
          val (newContent, res) = combine(self, l, newContentR)
          (Some(newContent), res)
        case Empty() =>
          (Some(newContentR), AllDone)
        case _: RDefined[A] | BiDef(_, _) | Slated(_, _) | Consumed() =>
          (None, AllDone)
      }
  }

  def lReciprocateLInvert[A, B]: (CellContent[A], LReciprocateLInvert[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (invSrcContent, inversion) =>
      val LReciprocateLInvert(self, inv, invTgt) = inversion

      def newContentL = LInvertSrc(inv, invTgt)

      invSrcContent match {
        case Empty() =>
          (Some(newContentL), AllDone)
        case r: RDefined[A] =>
          val (newContent, res) = combine(self, newContentL, r)
          (Some(newContent), res)
        case _: LDefined[A] | BiDef(_, _) | Slated(_, _) | Consumed() =>
          (None, AllDone)
      }
  }

  def propagateLCompletionRight[A, B]: (CellContent[B], PropagateLCompletionRight[A, B]) => (CellContent[B], ActionResult) = {
    (rContent, refinement) =>
      val PropagateLCompletionRight(src, payload, self) = refinement

      def checkL(l: LDefined[B]): Unit =
        l match {
          case LFwd(expectedSrc) =>
            if (!(src eq expectedSrc))
              throw IllegalStateException(s"Unexpected source of incoming l-completion ${addr(src)}, expected ${addr(expectedSrc)}")
          case LSkippingLeftLeft(newTgt, oldTgt) =>
            if (!((newTgt eq src) || (oldTgt eq src)))
              throw IllegalStateException(s"Neither old (${addr(oldTgt)}) nor new (${addr(newTgt)}) target of LSkippingLeftLeft is the source ${addr(src)} of incoming l-completion.")
          case LSkippingLeftUp(invSrc, lInv, oldTgt) =>
            if (!(oldTgt eq src))
              throw IllegalStateException(s"Unexpected source of incoming l-completion ${addr(src)}, expected ${addr(oldTgt)}.")
          case LSkippingLeftDown(invTgt, lInv, oldTgt) =>
            if (!(oldTgt eq src))
              throw IllegalStateException(s"Unexpected source of incoming l-completion ${addr(src)}, expected ${addr(oldTgt)}.")
          case LSkippingUpUp(newSrc, rInv, oldSrc, lInv) =>
            if (!(newSrc eq src))
              throw IllegalStateException(s"Unexpected source of incoming l-completion ${addr(src)}, expected ${addr(newSrc)}")
          case LValTgt(expectedSrc) =>
            if (!(src eq expectedSrc))
              throw IllegalStateException(s"Unexpected source of incoming l-completion ${addr(src)}, expected ${addr(expectedSrc)}")
          case LLiftedEither(expectedSrc) =>
            if (!(src eq expectedSrc))
              throw IllegalStateException(s"Unexpected source of incoming l-completion ${addr(src)}, expected ${addr(expectedSrc)}")
          case LDoneTgt(expectedSrc) =>
            if (!(src eq expectedSrc))
              throw IllegalStateException(s"Unexpected source of incoming l-completion ${addr(src)}, expected ${addr(expectedSrc)}")
        }

      rContent match {
        case l: LDefined[B] =>
          checkL(l)
          (payload, AllDone)
        case BiDef(l, r) =>
          checkL(l)
          combineLCompleteRDefined(self, payload, r)
        case Slated(l, r) =>
          checkL(l)
          combineLCompleteRDefined(self, payload, r)
        case PropagatingRCompletion(l, r) =>
          checkL(l)
          (Consumed(), combineLCompleteRComplete(payload, r))
        case r: RDefined[B] =>
          combineLCompleteRDefined(self, payload, r)
        case Empty() =>
          (payload, AllDone)
        case Consumed() =>
          (Consumed(), AllDone)
      }
  }

  def propagateRCompletionLeft[A]: (CellContent[A], PropagateRCompletionLeft[A]) => (CellContent[A], ActionResult) = {
    (lContent, propagation) =>
      val PropagateRCompletionLeft(self, payload, src) = propagation

      def checkR(r: RDefined[A]): Unit =
        r match {
          case RFwd(expectedSrc) =>
            if (!(src eq expectedSrc))
              throw IllegalStateException(s"Completion coming from unexpected source ${addr(src)}, expected ${addr(expectedSrc)}")
        }

      def finishPropagation = ConsumeAfterPropagationComplete(src)

      lContent match {
        case r: RDefined[A] =>
          checkR(r)
          (payload, finishPropagation)
        case BiDef(l, r) =>
          checkR(r)
          val (newContent, action) = combineLDefinedRComplete(self, l, payload)
          (newContent, finishPropagation and_? action)
        case Slated(l, r) =>
          checkR(r)
          val (newContent, action) = combineLDefinedRComplete(self, l, payload)
          (newContent, finishPropagation and_? action)
        case l: LDefined[A] =>
          val (newContent, action) = combineLDefinedRComplete(self, l, payload)
          (newContent, finishPropagation and_? action)
        case Empty() =>
          (payload, finishPropagation)
        case Consumed() =>
          (Consumed(), AllDone)
        case PropagatingLCompletion(l, r) =>
          throw IllegalStateException(s"Propagation from left to right did not consume the cell ${addr(self)} right away, but left it as $lContent. A concurrent $propagation now received from the right.")
          // checkR(r)
          // (Consumed(), combineLCompleteRComplete(l, payload))
      }
  }

  def refineRRole[A, B]: (CellContent[A], RefineRRole[A, B]) => (CellContent[A], ActionResult) = {
    (lContent, refinement) =>
      val RefineRRole(self, rRole, expectedRCell, payload) = refinement

      def goR(r: RDefined[A]): RComplete[A] = {
        r match {
          case r @ RRole(rRole1, rTgt) =>
            if ((rTgt eq expectedRCell) && (rRole1 == rRole))
              payload
            else
              throw new IllegalStateException(s"Actual $r did not equal expected ${RRole(rRole, expectedRCell)}")
        }
      }

      def goBi(l: LDefined[A], r: RDefined[A]): (CellContent[A], ActionResult) = {
        val r1 = goR(r)
        combineLDefinedRComplete(self, l, r1)
      }

      lContent match {
        case r @ RRole(rRole1, rTgt) =>
          if ((rTgt eq expectedRCell) && (rRole1 == rRole))
            (payload, AllDone)
          else
            throw new IllegalStateException(s"Actual $r did not equal expected ${RRole(rRole, expectedRCell)}")
        case BiDef(l, r) =>
          goBi(l, r)
        case Slated(l, r) =>
          goBi(l, r)
        case l: LDefined[A] =>
          combineLDefinedRComplete(self, l, payload)
        case Empty() =>
          (payload, AllDone)
      }
  }

  def refineLRole[A, B]: (CellContent[B], RefineLRole[A, B]) => (CellContent[B], ActionResult) = {
    (rContent, refinement) =>
      val RefineLRole(lCell, lRole, self, payload) = refinement

      def goL(l: LDefined[B]): LComplete[B] =
        l match {
          case LRole(lTgt, role) =>
            assert((lCell eq lTgt) && (lRole == role), s"Unexpected ${LRole(lCell, lRole)}, expected $l")
            payload
        }

      rContent match {
        case l: LDefined[B] =>
          (goL(l), AllDone)
        case BiDef(l, r) =>
          combineLCompleteRDefined(self, goL(l), r)
        case Empty() =>
          (payload, AllDone)
      }
  }

  def refineLPart[A, B]: (CellContent[B], RefineLPart[A, B]) => (Option[CellContent[B]], ActionResult) = {
    import RoleR._

    (rContent, refinement) =>
      val RefineLPart(lCell, rRole, self, payload) = refinement

      def checkL(expected: Cell[A]): Unit =
        assert(lCell eq expected, s"Unexpected source ${addr(lCell)} of $rRole in ${addr(self)}, expected ${addr(expected)}")

      def goL(l: LDefined[B]): LDefined[B] =
        rRole match {
          case RoleR.Joiner1 =>
            l match
              case JoinOf(src1, src2) =>
                checkL(src1)
                payload match
                  case DoneSupplied => Join2(src2)
              case Join1(src1) =>
                checkL(src1)
                payload match
                  case DoneSupplied => DoneSupplied
          case RoleR.Joiner2 =>
            l match
              case JoinOf(src1, src2) =>
                checkL(src2)
                payload match
                  case DoneSupplied => Join1(src1)
              case Join2(src2) =>
                checkL(src2)
                payload match
                  case DoneSupplied => DoneSupplied
          case RoleR.ZipVal1() =>
            l match
              case LZipVal(src1, src2) =>
                checkL(src1)
                payload match
                  case ValSupplied(x) => LZipVal2(x, src2)
              case LZipVal1(src1, y) =>
                checkL(src1)
                payload match
                  case ValSupplied(x) => ValSupplied((x, y))
          case RoleR.ZipVal2() =>
            l match
              case LZipVal(src1, src2) =>
                checkL(src2)
                payload match
                  case ValSupplied(y) => LZipVal1(src1, y)
              case LZipVal2(x, src2) =>
                checkL(src2)
                payload match
                  case ValSupplied(y) => ValSupplied((x, y))
          case RoleR.StrengthenPingSrc =>
            l match
              case LStrengthenedPing(src) =>
                checkL(src)
                payload match
                  case PingSupplied => DoneSupplied
          case _: RoleR.InjectionTrigger[x, y] =>
            l match
              case InjectLOnPing(triggerCell, cellToInject) =>
                checkL(triggerCell)
                payload match
                  case PingSupplied => InjectedL[x, y](cellToInject)
        }

      rContent match {
        case BiDef(l, r) =>
          val (newContent, res) = combine(self, goL(l), r)
          (Some(newContent), res)
        case l: LDefined[B] =>
          val newContent = goL(l)
          (Some(newContent), AllDone)
        case Empty() =>
          throw new IllegalStateException(s"Unexpected empty cell linked to by $rRole from ${addr(lCell)}")
      }
  }

  def refineRPart[A, B]: (CellContent[A], RefineRPart[A, B]) => (Option[CellContent[A]], ActionResult) = {
    import RoleL._

    (lContent, refinement) =>
      val RefineRPart(self, lRole, expectedRCell, payload) = refinement

      def goR(r: RDefined[A]): RDefined[A] | None.type =
        lRole match {
          case JoinerNeed1 =>
            r match
              case JoinNeedOf(src1, src2) =>
                assert(expectedRCell eq src1)
                payload match
                  case NeedSupplied => JoinNeed2(src2)
              case JoinNeed1(src1) =>
                assert(expectedRCell eq src1)
                payload match
                  case NeedSupplied => NeedSupplied
              case JoinPong2(_) =>
                throw IllegalStateException(s"Double arrival of first Need joiner")
          case JoinerNeed2 =>
            r match
              case JoinNeedOf(src1, src2) =>
                assert(expectedRCell eq src2)
                payload match
                  case NeedSupplied => JoinNeed1(src1)
              case JoinNeed2(src2) =>
                assert(expectedRCell eq src2)
                payload match
                  case NeedSupplied => NeedSupplied
              case JoinNeed1(src1) =>
                throw IllegalStateException(s"Double arrival of second Need joiner")
          case JoinerPong1 =>
            r match
              case JoinPongOf(src1, src2) =>
                assert(expectedRCell eq src1)
                payload match
                  case PongSupplied => JoinPong2(src2)
              case JoinPong1(src1) =>
                assert(expectedRCell eq src1)
                payload match
                  case PongSupplied => PongSupplied
              case JoinPong2(_) =>
                throw IllegalStateException(s"Double arrival of first Pong joiner")
          case JoinerPong2 =>
            r match
              case JoinPongOf(src1, src2) =>
                assert(expectedRCell eq src2)
                payload match
                  case PongSupplied => JoinPong1(src1)
              case JoinPong2(src2) =>
                assert(expectedRCell eq src2)
                payload match
                  case PongSupplied => PongSupplied
              case JoinPong1(src1) =>
                throw IllegalStateException(s"Double arrival of second Pong joiner")
          case SelectContestant1 =>
            r match
              case SelectOf(contestant1, contestant2) =>
                assert(contestant1 eq expectedRCell)
                payload match
                  case PongSupplied => ChosenL[One, One](Cell.one)
              case ChosenR(_) =>
                // already lost the race
                payload match
                  case PongSupplied => None
          case SelectContestant2 =>
            r match
              case SelectOf(contestant1, contestant2) =>
                assert(contestant2 eq expectedRCell)
                payload match
                  case PongSupplied => ChosenR[One, One](Cell.one)
              case ChosenL(rCell) =>
                // already lost the race
                payload match
                  case PongSupplied => None

        }

      lContent match {
        case BiDef(l, r) =>
          goR(r) match
            case r: RDefined[A] =>
              val (newContent, res) = combine(self, l, r)
              (Some(newContent), res)
            case None =>
              (None, AllDone)
        case Slated(l, r) =>
          // may be slated, because we contract the cell if awaiting last joiner
          goR(r) match
            case r: RDefined[A] =>
              val (newContent, res) = combine(self, l, r)
              (Some(newContent), res)
            case None =>
              (None, AllDone)
        case PropagatingRCompletion(l, r) =>
          goR(r) match
            case None =>
              (None, AllDone)
            case r: RDefined[A] =>
              throw IllegalStateException(s"Did not expect refinement of $lContent by $refinement to have an effect, but resulted in $r")
        case r: RDefined[A] =>
          goR(r) match
            case None           => (None, AllDone)
            case r: RDefined[A] => (Some(r), AllDone)
        case Consumed() =>
          (None, AllDone)
        case Empty() =>
          throw new IllegalStateException(s"Unexpected empty cell linked to by $lRole from $expectedRCell")
      }
  }

  def propagateLCompletionUp[A, B]: (CellContent[A], PropagateLCompletionUp[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (invSrcContent, propagation) =>
      val PropagateLCompletionUp(self, payload, rInv, invTgt) = propagation

      def checkR(r: RDefined[A]): Unit =
        r match {
          case RInvertSrc(i, tgt) =>
            assert(rInv == i, s"Unexpected inversion $rInv, expected $i")
            assert(invTgt eq tgt, s"Unexpected r-inversion target ${addr(invTgt)}, expected ${addr(tgt)}")
          case RSkippingDownLeft(i, oldTgt, newTgt) =>
            assert(rInv == i, s"Unexpected inversion $rInv, expected $i")
            assert(
              (invTgt eq oldTgt) || (invTgt eq newTgt),
              s"Unexpected r-inversion target ${addr(invTgt)}, expected ${addr(oldTgt)} or ${addr(newTgt)}"
            )
        }

      def nextStep = ConsumeAfterPropagationComplete(invTgt)

      invSrcContent match {
        case r: RDefined[A] =>
          checkR(r)
          (Some(payload), nextStep)
        case BiDef(l, r) =>
          checkR(r)
          val (newContent, res) = combine(self, l, payload)
          (Some(newContent), nextStep and_? res)
        case Slated(l, r) =>
          checkR(r)
          val (newContent, res) = combine(self, l, payload)
          (Some(newContent), nextStep and_? res)
        case l: LDefined[A] =>
          val (newContent, res) = combine(self, l, payload)
          (Some(newContent), nextStep and_? res)
        case Consumed() =>
          (None, AllDone)
      }
  }

  def refineRInvertTgt[A, B]: (CellContent[B], RefineRInvertTgt[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (invTgtContent, refinement) =>
      val RefineRInvertTgt(invSrc, rInv, self, payload) = refinement

      def checkR(r: RDefined[B]): Unit =
        r match {
          case RInvertTgt(src, rInv1) =>
            assert(rInv == rInv1, s"Unexpected inversion $rInv, expected $rInv1")
            assert(invSrc eq src, s"Unexpected r-inversion source ${addr(invSrc)}, expected ${addr(src)}")
          case RSkippingUpLeft(newSrc, oldSrc, rInv1) =>
            assert(rInv == rInv1, s"Unexpected inversion $rInv, expected $rInv1")
            assert(
              (invSrc eq newSrc) || (invSrc eq oldSrc),
              s"Unexpected r-inversion source ${addr(invSrc)}, expected ${addr(newSrc)} or ${addr(oldSrc)}",
            )
        }

      invTgtContent match {
        case r: RDefined[B] =>
          checkR(r)
          (Some(payload), AllDone)
        case BiDef(l, r) =>
          checkR(r)
          val (content, res) = combineLDefinedRComplete(self, l, payload)
          (Some(content), res)
        case Slated(l, r) =>
          checkR(r)
          val (content, res) = combineLDefinedRComplete(self, l, payload)
          (Some(content), res)
        case Empty() =>
          (Some(payload), AllDone)
        case PropagatingLCompletion(l, r) =>
          checkR(r)
          val res = combineLCompleteRComplete(l, payload)
          (Some(Consumed()), res)
        case Consumed() =>
          (None, AllDone)
      }
  }

  def propagateRCompletionUp[A, B]: (CellContent[A], PropagateRCompletionUp[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (invSrcContent, propagation) =>
      val PropagateRCompletionUp(self, payload, lInv, invTgt) = propagation

      def checkL(l: LDefined[A]): Unit = {
        def go[X](i: Inversion[X, A], tgt: Cell[X]): Unit =
          assert(invTgt eq tgt, s"Unexpected l-inversion target ${addr(invTgt)}, expected ${addr(tgt)}")
          assert(lInv == i, s"Unexpected inversion $lInv, expected $i")

        l match {
          case LInvertSrc(i, tgt)                => go(i, tgt)
          case LSkippingLeftDown(tgt, i, oldTgt) => go(i, tgt)
        }
      }

      def nextStep = ConsumeAfterPropagationComplete(invTgt)

      invSrcContent match {
        case l: LDefined[A] =>
          checkL(l)
          (Some(payload), nextStep)
        case BiDef(l, r) =>
          checkL(l)
          val (content, res) = combineLCompleteRDefined(self, payload, r)
          (Some(content), nextStep and_? res)
        case Slated(l, r) =>
          checkL(l)
          val (content, res) = combineLCompleteRDefined(self, payload, r)
          (Some(content), nextStep and_? res)
        case r: RDefined[A] =>
          val (content, res) = combineLCompleteRDefined(self, payload, r)
          (Some(content), nextStep and_? res)
        case Consumed() =>
          (None, AllDone)
        case Empty() =>
          (Some(payload), nextStep)
      }
  }

  def propagateRCompletionDown[A, B]: (CellContent[B], PropagateRCompletionDown[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (invTgtContent, propagation) =>
      val PropagateRCompletionDown(invSrc, lInv, payload, self) = propagation

      def checkL(l: LDefined[B]): Unit = {
        def go[X](invSrc0: Cell[X], lInv0: Inversion[B, X]): Unit =
          assert(invSrc eq invSrc0, s"Unexpected l-inversion source ${addr(invSrc)}, expected ${addr(invSrc0)}")
          assert(lInv == lInv0, s"Unexpected inversion $lInv, expected $lInv0")

        l match {
          case LInvertTgt(src, i)           => go(src, i)
          case LInvertTgtClaimed(src, i)    => go(src, i)
          case LSkippingLeftUp(src, i, _)   => go(src, i)
          case LSkippingUpUp(_, _, src0, j) => go(src0, j)
        }
      }

      invTgtContent match {
        case BiDef(l, r) =>
          checkL(l)
          val (content, res) = combineLCompleteRDefined(self, payload, r)
          (Some(content), res)
        case Slated(l, r) =>
          checkL(l)
          val (content, res) = combineLCompleteRDefined(self, payload, r)
          (Some(content), res)
        case PropagatingRCompletion(l, r) =>
          checkL(l)
          val res = combineLCompleteRComplete(payload, r)
          (Some(Consumed()), res)
        case l: LDefined[B] =>
          checkL(l)
          (Some(payload), AllDone)
        case Empty() =>
          (Some(payload), AllDone)
        case Consumed() =>
          (None, AllDone)
      }
  }

  @tailrec
  private def combineLCompleteRComplete[A](l: LComplete[A], r: RComplete[A]): ActionResult =
    l match {
      case DoneSupplied =>
        r match
          case DoneCallback(f) => CallbackTriggered(f, Right(()))
      case NeedCallback(f) =>
        r match
          case NeedSupplied => CallbackTriggered(f, Right(()))
      case InjectedL(injectedCell) =>
        r match
          case EitherCallback(f) => CallbackTriggered(f, Right(Left(injectedCell)))
      case InjectedR(injectedCell) =>
        r match
          case EitherCallback(f) => CallbackTriggered(f, Right(Right(injectedCell)))
      case LSplit(a1, a2) =>
        r match
          case RSplit(b1, b2) => UnificationRequest(a1, b1) and UnificationRequest(a2, b2)
      case LCompleteInv(r1) =>
        r match
          case RCompleteInv(l1) =>
            combineLCompleteRComplete(l1, r1)
          case RSplitInv(x, y) =>
            r1 match
              case RSplit(cell1, cell2) =>
                LInvert(x, Inversion.Universal(), cell1) and
                LInvert(y, Inversion.Universal(), cell2)
      case LInvertTgtPair(nx, ny) =>
        r match
          case RSplit(x, y) =>
            LInvert(nx, Inversion.Universal(), x) and
            LInvert(ny, Inversion.Universal(), y)
    }

  private def combineLDefinedRComplete[A](self: Cell[A], l: LDefined[A], r: RComplete[A]): (CellContent[A], ActionResult) =
    r match {
      case r @ DoneCallback(listener) =>
        l match
          case DoneSupplied               => (Consumed(), CallbackTriggered(listener, Right(())))
          case l: JoinOf                  => (BiDef(l, r), AllDone)
          case l: Join1                   => (BiDef(l, r), AllDone)
          case l: Join2                   => (BiDef(l, r), AllDone)
          case l: LDoneTgt[x]             => (BiDef(l, r), AllDone)
          case l @ LFwd(lTgt)             => (PropagatingRCompletion(l, r), PropagateRCompletionLeft(lTgt, r, self))
          case LInvertTgt(src, i)         => (PropagatingRCompletion(l, r), PropagateRCompletionUp(src, r.lInvert(i), i, self))
          case l: LInvertTgtClaimed[x, A] => (BiDef(l, r), AllDone)
          case l: LSkippingLeftLeft[A]    => (BiDef(l, r), AllDone)
          case l: LSkippingUpUp[A, x]     => (BiDef(l, r), AllDone)
          case l: LSkippingLeftUp[x, A]   => (BiDef(l, r), AllDone)
      case cb @ EitherCallback(listener) =>
        l match
          case InjectedL(cell) => (Consumed(), CallbackTriggered(listener, Right(Left(cell))))
          case InjectedR(cell) => (Consumed(), CallbackTriggered(listener, Right(Right(cell))))
      case r @ ChosenR(resultCell) =>
        l match
          case ChooseFrom(lTgt, _, g)  => (Consumed(), ConnectionRequest(lTgt, g, resultCell))
          case ChoiceWith(lTgt, add)   => (Consumed(), ChooseR(lTgt, Cell(RSplit(add, resultCell))))
          case LFwd(lTgt)              => (PropagatingRCompletion(l, r), PropagateRCompletionLeft(lTgt, r, self))
          case LInvertTgt(iSrc, i)     => (PropagatingRCompletion(l, r), PropagateRCompletionUp(iSrc, r.lInvert(i), i, self))
          case l: LInvertTgtClaimed[x, A] => (BiDef(l, r), AllDone)
          case l: LSkippingLeftLeft[A]    => (BiDef(l, r), AllDone)
          case l: LSkippingLeftUp[x, A]   => (BiDef(l, r), AllDone)
          case l: LSkippingUpUp[A, x]     => (BiDef(l, r), AllDone)
          case l: LNotifyChoice[x, y]  =>
            import RoleR.{ChoiceNotification, NotifyChoiceTgt}
            val followUp =
              RefineRRole[Pong, x |&| y](l.notification, ChoiceNotification(), expectedRTarget = self, PongSupplied) and
              RefineRRole(l.tgt, NotifyChoiceTgt(), expectedRTarget = self, r)
            (Consumed(), followUp)
      case r @ ChosenL(resultCell) =>
        l match
          case ChooseFrom(lTgt, f, _)  => (Consumed(), ConnectionRequest(lTgt, f, resultCell))
          case ChoiceWith(lTgt, add)   => (Consumed(), ChooseL(lTgt, Cell(RSplit(add, resultCell))))
          case LFwd(lTgt)              => (PropagatingRCompletion(l, r), PropagateRCompletionLeft(lTgt, r, self))
          case LInvertTgt(iSrc, i)     => (PropagatingRCompletion(l, r), PropagateRCompletionUp(iSrc, r.lInvert(i), i, self))
          case l: LSkippingLeftLeft[A] => (BiDef(l, r), AllDone)
          case l: LSkippingLeftUp[x, A]   => (BiDef(l, r), AllDone)
          case l: LSkippingUpUp[A, x]     => (BiDef(l, r), AllDone)
          case l: LNotifyChoice[x, y]  =>
            import RoleR.{ChoiceNotification, NotifyChoiceTgt}
            val followUp =
              RefineRRole[Pong, x |&| y](l.notification, ChoiceNotification(), expectedRTarget = self, PongSupplied) and
              RefineRRole(l.tgt, NotifyChoiceTgt(), expectedRTarget = self, r)
            (Consumed(), followUp)
      case NeedSupplied =>
        l match
          case LFwd(lTgt)                 => (PropagatingRCompletion(l, r), PropagateRCompletionLeft(lTgt, r, self))
          case LInvertSrc(i, tgt)         => (Consumed(), PropagateRCompletionDown(self, i, NeedSupplied.lUnInvert(i), tgt))
          case LInvertTgt(src, i)         => (PropagatingRCompletion(l, r), PropagateRCompletionUp(src, NeedSupplied.lInvert(i), i, self))
          case l: LInvertTgtClaimed[x, A] => (BiDef(l, r), AllDone)
          case l: LSkippingLeftLeft[A]    => (BiDef(l, r), AllDone)
          case l: LSkippingUpUp[A, y]     => (BiDef(l, r), AllDone)
          case l: LSkippingLeftUp[x, A]   => (BiDef(l, r), AllDone)
          case l: LSkippingLeftDown[x, A] => (BiDef(l, r), AllDone)
          case LRole(lTgt, lRole)         => (Consumed(), RefineRPart(lTgt, lRole, self, NeedSupplied))
          case NeedCallback(f)            => (Consumed(), CallbackTriggered(f, Right(())))
          case l: LNotifyNeed =>
            import RoleR.{NeedNotification, NotifyNeedTgt}
            val followUp =
              RefineRRole(l.notification, NeedNotification, expectedRTarget = self, PongSupplied) and
              RefineRRole(l.tgt, NotifyNeedTgt, expectedRTarget = self, NeedSupplied)
            (Consumed(), followUp)
      case PongSupplied =>
        l match
          case LFwd(lTgt)                  => (PropagatingRCompletion(l, r), PropagateRCompletionLeft(lTgt, r, self))
          case LInvertSrc(i, tgt)          => (Consumed(), PropagateRCompletionDown(self, i, PongSupplied.lUnInvert(i), tgt))
          case LInvertTgt(src, i)          => (PropagatingRCompletion(l, r), PropagateRCompletionUp(src, r.lInvert(i), i, self))
          case LRole(lTgt, lRole)          => (Consumed(), RefineRPart(lTgt, lRole, expectedRTarget = self, PongSupplied))
          case l: LInvertTgtClaimed[x, A]  => (BiDef(l, r), AllDone)
          case l: LSkippingLeftLeft[A]     => (BiDef(l, r), AllDone)
          case l: LSkippingLeftUp[x, A]    => (BiDef(l, r), AllDone)
          case l: LSkippingUpUp[A, y]      => (BiDef(l, r), AllDone)
          case l: LSkippingLeftDown[x, A]  => (BiDef(l, r), AllDone)
          case l: LSkippingLeftLRole[x, A] => (BiDef(l, r), AllDone)
      case r: RCompleteInv[x] =>
        l match
          case LFwd(lTgt)                 => (PropagatingRCompletion(l, r), PropagateRCompletionLeft(lTgt, r, self))
          case LInvertSrc(i, tgt)         => (Consumed(), PropagateRCompletionDown(self, i, r.lUnInvert(i), tgt))
          case LInvertTgt(src, i)         => (PropagatingRCompletion(l, r), PropagateRCompletionUp(src, r.lInvert(i), i, self))
          case l: LSkippingLeftLeft[A]    => (BiDef(l, r), AllDone)
          case l: LSkippingLeftUp[x, A]   => (BiDef(l, r), AllDone)
          case l: LSkippingLeftDown[x, A] => (BiDef(l, r), AllDone)
          case l: LSkippingUpUp[A, y]     => (BiDef(l, r), AllDone)
          case l: LInvertTgtClaimed[x, A] => (BiDef(l, r), AllDone)
          case l: LCompleteInv[y]         => (Consumed(), combineLCompleteRComplete(r.src, l.src))
      case r: RSplit[x, y] =>
        combineLDefinedRSplit[x, y](self, l, r)
      case r: RSplitInv[x, y] =>
        combineLDefinedRSplitInv[x, y](self, l, r)
    }

  private def combineLCompleteRDefined[A](self: Cell[A], l: LComplete[A], r: RDefined[A]): (CellContent[A], ActionResult) =
    l match {
      case DoneSupplied =>
        r match
          case RFwd(tgt) =>
            (Consumed(), PropagateLCompletionRight(self, l, tgt))
          case RInvertSrc(inv, tgt) =>
            (Consumed(), RefineRInvertTgt(expectedInvSrc = self, inv, tgt, DoneSupplied.rInvert(inv)))
          case r: RSkippingDownLeft[A, y] =>
            (BiDef(l, r), AllDone)
          case RRole(role, tgt) =>
            (Consumed(), RefineLPart(self, role, tgt, DoneSupplied))
          case RConstVal(a, tgt) =>
            (Consumed(), PropagateLCompletionRight(self, ValSupplied(a), tgt))
          case RNotifyDone(nCell, tgtCell) =>
            val followUp =
              RefineLRole(self, RoleL.DoneNotification, nCell, PingSupplied) and
              RefineLRole(self, RoleL.NotifyDoneTgt, tgtCell, DoneSupplied)
            (Consumed(), followUp)
          case DoneCallback(f) =>
            (Consumed(), CallbackTriggered(f, Right(())))

      case PingSupplied =>
        r match
          case RFwd(tgt) =>
            (Consumed(), PropagateLCompletionRight(self, l, tgt))
          case RInvertSrc(inv, tgt) =>
            (Consumed(), RefineRInvertTgt(expectedInvSrc = self, inv, tgt, PingSupplied.rInvert(inv)))
          case r: RSkippingDownLeft[A, y] =>
            (BiDef(l, r), AllDone)
          case RRole(role, tgt) =>
            (Consumed(), RefineLPart(self, role, tgt, PingSupplied))

      case l: ValSupplied[a] =>
        r match
          case r: RMapValSrc[`a`, y] =>
            (Consumed(), MapValTriggered[a, y](self, l.value, r.f, r.tgt))
          case RFwd(tgt) =>
            (Consumed(), PropagateLCompletionRight(self, l, tgt))
          case RInvertSrc(inv, tgt) =>
            (Consumed(), RefineRInvertTgt(expectedInvSrc = self, inv, tgt, l.rInvert(inv)))
          case r: RSkippingDownLeft[A, y] =>
            (BiDef(l, r), AllDone)
          case r: RLiftEither[x, y] =>
            val l1: LComplete[Val[x] |+| Val[y]] = l.value match
              case Left(x)  => InjectedL(Cell(ValSupplied(x)))
              case Right(y) => InjectedR(Cell(ValSupplied(y)))
            (Consumed(), PropagateLCompletionRight(self, l1, r.tgt))
          case RNeglectVal(tgt) =>
            (Consumed(), PropagateLCompletionRight(self, DoneSupplied, tgt))
          case RRole(role, tgt) =>
            (Consumed(), RefineLPart(self, role, tgt, l))

      case l @ NeedCallback(f) =>
        r match
          case RFwd(tgt) =>
            (Consumed(), PropagateLCompletionRight(self, l, tgt))
          case NeedSupplied =>
            (Consumed(), CallbackTriggered(f, Right(())))
          case RInvertSrc(i, tgt) =>
            (Consumed(), RefineRInvertTgt(self, i, tgt, l.rInvert(i)))
          case RInvertTgt(src, i) =>
            (PropagatingLCompletion(l, r), PropagateLCompletionUp(src, l.rUnInvert(i), i, self))
          case r: RSkippingDownLeft[A, y] =>
            (BiDef(l, r), AllDone)
          case r: RSkippingUpLeft[x, A] =>
            (BiDef(l, r), AllDone)

      case l @ InjectedL(lCell) =>
        r match
          case EitherSwitch(f, g, rCell) =>
            (Consumed(), ConnectionRequest(lCell, f, rCell))
          case r: RNotifyEither[x, y] =>
            val followUp =
              RefineLRole(self, RoleL.EitherNotification[x, y](), r.notificationCell, PingSupplied) and
              RefineLRole(self, RoleL.NotifyEitherTgt[x, y](), r.outCell, l)
            (Consumed(), followUp)
          case EitherWith(addendum, tgt) =>
            (Consumed(), InjectL(Cell(LSplit(addendum, lCell)), tgt))
          case RFwd(rTgt) =>
            (Consumed(), PropagateLCompletionRight(self, l, rTgt))
          case RInvertSrc(i, iTgt) =>
            (Consumed(), RefineRInvertTgt(self, i, iTgt, l.rInvert(i)))
          case r: RSkippingDownLeft[A, y] =>
            (BiDef(l, r), AllDone)

      case l @ InjectedR(lCell) =>
        r match
          case EitherSwitch(f, g, rCell) =>
            (Consumed(), ConnectionRequest(lCell, g, rCell))
          case r: RNotifyEither[x, y] =>
            val followUp =
              RefineLRole(self, RoleL.EitherNotification[x, y](), r.notificationCell, PingSupplied) and
              RefineLRole(self, RoleL.NotifyEitherTgt[x, y](), r.outCell, l)
            (Consumed(), followUp)
          case EitherWith(addendum, tgt) =>
            (Consumed(), InjectR(Cell(LSplit(addendum, lCell)), tgt))
          case RFwd(rTgt) =>
            (Consumed(), PropagateLCompletionRight(self, l, rTgt))
          case RInvertSrc(i, iTgt) =>
            (Consumed(), RefineRInvertTgt(self, i, iTgt, l.rInvert(i)))
          case r: RSkippingDownLeft[A, y] =>
            (BiDef(l, r), AllDone)

      case l: LSplit[x, y] =>
        combineLSplitRDefined[x, y](self, l, r)

      case l: LCompleteInv[x] =>
        r match
          case RFwd(rTgt) =>
            (Consumed(), PropagateLCompletionRight(self, l, rTgt))
          case RInvertSrc(i, tgt) =>
            (Consumed(), RefineRInvertTgt(self, i, tgt, l.rInvert(i)))
          case RInvertTgt(src, i) =>
            (PropagatingLCompletion(l, r), PropagateLCompletionUp(src, l.rUnInvert(i), i, self))
          case r: RSkippingDownLeft[A, y] =>
            (BiDef(l, r), AllDone)
          case r: RSkippingUpLeft[y, A] =>
            (BiDef(l, r), AllDone)
          case r: RCompleteInv[y] =>
            (Consumed(), combineLCompleteRComplete(r.src, l.src))
          case RSplitInv(c1, c2) =>
            l.src match
              case RSplit(cell1, cell2) =>
                (Consumed(), LInvert(c1, Inversion.Universal(), cell1) and LInvert(c2, Inversion.Universal(), cell2))

    }

  private def combineLDefinedRSplit[A, B](self: Cell[A |*| B], l: LDefined[A |*| B], r: RSplit[A, B]): (CellContent[A |*| B], ActionResult) =
    l match
      case LSplit(l1, l2)                => (Consumed(), UnificationRequest(l1, r.cell1) and UnificationRequest(l2, r.cell2))
      case LFwd(lTgt)                    => (PropagatingRCompletion(l, r), PropagateRCompletionLeft(lTgt, r, self))
      case LInvertTgt(invSrc, i)         => (PropagatingRCompletion(l, r), PropagateRCompletionUp(invSrc, r.lInvert(i), i, self))
      case l: LInvertTgtClaimed[x, A |*| B] => (BiDef(l, r), AllDone)
      case l: LSkippingLeftLeft[A |*| B]    => (BiDef(l, r), AllDone)
      case LInvertTgtPair(src1, src2)       => (Consumed(), LInvert(src1, Inversion.Universal(), r.cell1) and LInvert(src2, Inversion.Universal(), r.cell2))

  private def combineLDefinedRSplitInv[A, B](self: Cell[-[A |*| B]], l: LDefined[-[A |*| B]], r: RSplitInv[A, B]): (CellContent[-[A |*| B]], ActionResult) =
    l match
      case LCompleteInv(rComplete) =>
        rComplete match
          case RSplit(cell1, cell2) =>
            (Consumed(), LInvert(r.fst, Inversion.Universal(), cell1) and LInvert(r.snd, Inversion.Universal(), cell2))
      case LFwd(lTgt) =>
        (PropagatingRCompletion(l, r), PropagateRCompletionLeft(lTgt, r, self))
      case LInvertSrcPair(tgt1, tgt2) =>
        (Consumed(), LInvert(r.fst, Inversion.Universal(), tgt1) and LInvert(r.snd, Inversion.Universal(), tgt2))
      case LInvertSrc(i, tgt) =>
        (Consumed(), PropagateRCompletionDown(self, i, payload = r.lUnInvert(i), tgt))
      case LSkippingLeftDown(_, _, _) =>
        (BiDef(l, r), AllDone)
      case LSkippingLeftUp(_, _, _) =>
        (BiDef(l, r), AllDone)
      case LSkippingLeftLeft(_, _) =>
        (BiDef(l, r), AllDone)
      case LSkippingUpUp(_, _, _, _) =>
        (BiDef(l, r), AllDone)

  private def combineLSplitRDefined[A, B](self: Cell[A |*| B], l: LSplit[A, B], r: RDefined[A |*| B]): (CellContent[A |*| B], ActionResult) =
    r match
      case RSplit(r1, r2) => (Consumed(), UnificationRequest(l.cell1, r1) and UnificationRequest(l.cell2, r2))
      case RFwd(rTgt)     => (Consumed(), PropagateLCompletionRight(self, l, rTgt))

  private def combine[A](self: Cell[A], l: LDefined[A], r: RDefined[A]): (CellContent[A], ActionResult) =
    (l, r) match {
      case (l: LComplete[A], r)                       => combineLCompleteRDefined(self, l, r)
      case (l, r: RComplete[A])                       => combineLDefinedRComplete(self, l, r)
      case (l: LFwd[A], r: RFwd[A])                   => (Slated(l, r), ContractBiFwd(l.tgt, self, r.tgt))
      case (l: LFwd[A], r: RInvertSrc[A, b])          => (Slated(l, r), ContractLFwdRInvSrc(l.tgt, self, r.inv, r.tgt))
      case (l: LFwd[A], r: RInvertTgt[x, A])          => (Slated(l, r), ContractLFwdRInvTgt(l.tgt, self, r.inv, r.src))
      case (l: LInvertSrc[A, x], r: RFwd[A])          => (Slated(l, r), ContractLInvSrcRFwd(l.tgt, l.inv, self, r.tgt))
      case (l: LInvertSrc[A, x], r: RInvertTgt[y, A]) => (Slated(l, r), ContractLInvSrcRInvTgt.mk(r.src, r.inv, self, l.inv, l.tgt))
      case (l: LInvertTgt[x, A], r: RFwd[A])          => (Slated(l, r), ContractLInvTgtRFwd(l.src, l.inv, self, r.tgt))
      case (l: LInvertTgt[x, A], r: RInvertSrc[A, y]) => (BiDef(l, r), AllDone) // TODO: Do contract. Use Iso[x, y] in RFwd, LFwd
      case (l: LInvertSrc[A, x], r: RInvertSrc[A, y]) => (BiDef(l, r), AllDone)
      case (l: LInvertTgt[x, A], r: RInvertTgt[y, A]) => (BiDef(l, r), AllDone)
      case (l, r: RSkippingDownLeft[A, b])            => (BiDef(l, r), AllDone)
      case (l, r: RSkippingUpLeft[x, A])              => (BiDef(l, r), AllDone)
      case (l: LFwd[A], r: JoinPongOf)                => (BiDef(l, r), AllDone)
      case (l: LFwd[A], r: RMapValSrc[x, y])          => (BiDef(l, r), AllDone)
      case (l: LRole[x, A], r)                        => (BiDef(l, r), AllDone)
      case (l: JoinOf, r: RRole[A, b])                => (BiDef(l, r), AllDone)
      case (l: Join1, r: RRole[A, b])                 => (BiDef(l, r), AllDone)
      case (l: Join2, r: RRole[A, b])                 => (BiDef(l, r), AllDone)
      case (l: JoinOf, r: RFwd[A])                    => (BiDef(l, r), AllDone)
      case (l: Join1, r: RFwd[A])                     => (BiDef(l, r), AllDone)
      case (l: Join2, r: RFwd[A])                     => (BiDef(l, r), AllDone)
      case (l: LZipVal[x, y], r)                      => (BiDef(l, r), AllDone)
      case (l: LZipVal1[x, y], r)                     => (BiDef(l, r), AllDone)
      case (l: LZipVal2[x, y], r)                     => (BiDef(l, r), AllDone)
      case (l: LFwd[A], r: RRole[A, x])               => (BiDef(l, r), AllDone)
      case (l: LInvertSrc[A, x], r: RRole[A, y])      => (BiDef(l, r), AllDone)
      case (l: LInvertTgt[x, A], r: RRole[A, y])      => (BiDef(l, r), AllDone)
      case (l: LSkippingLeftLeft[A], r)               => (BiDef(l, r), AllDone)
      case (l: LSkippingLeftLRole[x, A], r)           => (BiDef(l, r), AllDone)
      case (l: LSkippingLeftUp[x, A], r)              => (BiDef(l, r), AllDone)
      case (l: LSkippingLeftDown[x, A], r)            => (BiDef(l, r), AllDone)
      case (l: LSkippingUpUp[A, x], r)                => (BiDef(l, r), AllDone)
      case (l @ LFwd(lTgt), r @ JoinNeed1(src))       => (Slated(l, r), ContractBiFwd(lTgt, slated = self, src))
      case (l @ LFwd(lTgt), r @ JoinNeed2(src))       => (Slated(l, r), ContractBiFwd(lTgt, slated = self, src))
      case (l @ LFwd(lTgt), r @ JoinPong1(src))       => (Slated(l, r), ContractBiFwd(lTgt, slated = self, src))
      case (l @ LFwd(lTgt), r @ JoinPong2(src))       => (Slated(l, r), ContractBiFwd(lTgt, slated = self, src))
      case (l: LFwd[A]         , r: EitherSwitch[a, b, c]) => (BiDef(l, r), AllDone)
      case (l: LInvertTgt[x, A], r: EitherSwitch[a, b, c]) => (BiDef(l, r), AllDone)
      case (l: LFwd[A]         , r: EitherWith[a, b, c])   => (BiDef(l, r), AllDone)
      case (l: LInvertTgt[x, A], r: EitherWith[a, b, c])   => (BiDef(l, r), AllDone)
      case (l: ChooseFrom[x, y, z], r: RFwd[A])       => (BiDef(l, r), AllDone)
      case (l: ChooseFrom[x, y, z], r: RRole[A, b])   => (BiDef(l, r), AllDone)
      case (l: ChooseFrom[x, y, z], r: RInvertSrc[A, b]) => (BiDef(l, r), AllDone)
      case (l: ChoiceWith[x, y, z], r: RFwd[A])       => (BiDef(l, r), AllDone)
      case (l: LNotifyNeed, r)                        => (BiDef(l, r), AllDone)
      case (l: LNotifyChoice[x, y], r)                => (BiDef(l, r), AllDone)
      case (l, r: RNotifyEither[x, y])                => (BiDef(l, r), AllDone)
      case (l, r: RNotifyDone)                        => (BiDef(l, r), AllDone)
      case (l: LInvertTgtClaimed[x, A], r)            => (BiDef(l, r), AllDone)
      case (l: LStrengthenedPing, r)                  => (BiDef(l, r), AllDone)
      case (l: LInvertTgt[x, A], r: RMapValSrc[a, b]) => (BiDef(l, r), AllDone)
      case (l, r: RConstVal[x])                       => (BiDef(l, r), AllDone)
      case (l, r: RNeglectVal[x])                     => (BiDef(l, r), AllDone) // TODO: propagate neglection towards the source
      case (l: LValTgt[x, a], r)                      => (BiDef(l, r), AllDone)
      case _ =>
        UnhandledCase.raise(s"($l, $r)")
    }

  def initBiFwdContraction[A]: (CellContent[A], ContractBiFwd[A]) => (Option[CellContent[A]], ActionResult) = {
    (rContent, contraction) =>
      val ContractBiFwd(lCell, mCell, rCell) = contraction

      def lStillCurrent(l: LDefined[A]): Boolean = {
        def goTgt[X](lTgt: Cell[X]): Boolean =
          lTgt eq mCell

        l match {
          case LFwd(tgt)                      => goTgt(tgt)
          case LRole(tgt, _)                  => goTgt(tgt)
          case LSkippingLeftLeft(newTgt, _)   => goTgt(newTgt)
          case LSkippingUpUp(newSrc, _, _, _) => goTgt(newSrc)
          case _: LComplete[A]                => false
        }
      }

      def newContentL = LSkippingLeftLeft(lCell, mCell)
      def followUp    = SkipAhead(contraction)

      rContent match {
        case Empty() =>
          (Some(newContentL), followUp)
        case l: LDefined[A] =>
          if (lStillCurrent(l)) (Some(newContentL), followUp)
          else                  (None, AllDone)
        case BiDef(l, r) =>
          if (lStillCurrent(l)) (Some(BiDef(newContentL, r)), followUp)
          else                  (None, AllDone)
        case r: RDefined[A] =>
          (Some(BiDef(newContentL, r)), followUp)
        case Slated(_, _) => // obstructed
          (None, AllDone)
        case PropagatingRCompletion(_, _) | PropagatingLCompletion(_, _) | Consumed() => // overtaken
          (None, AllDone)
      }
  }

  def initLFwdRInvTgtContraction[A, B]: (CellContent[B], ContractLFwdRInvTgt[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (invSrcContent, contraction) =>
      val ContractLFwdRInvTgt(lCell, slatedRInvTgt, rInv, rInvSrc) = contraction

      def newContentR = RSkippingDownLeft(rInv, oldTgt = slatedRInvTgt, newTgt = lCell)
      def followUp    = SkipToRInvSrc(contraction)

      def goR(r: RDefined[B]): Option[RDefined[B]] = {
        r match
          case RInvertSrc(i, tgt) =>
            assert(i == rInv, s"Unexpected inversion $rInv, expected $i")
            if (tgt eq slatedRInvTgt)
              Some(newContentR)
            else
              None
          case RSkippingDownLeft(i, _, newTgt) =>
            assert(i == rInv, s"Unexpected inversion $rInv, expected $i")
            if (newTgt eq slatedRInvTgt)
              Some(newContentR)
            else
              None
          case _: RComplete[B] =>
            None
      }

      invSrcContent match {
        case Empty() =>
          (Some(newContentR), followUp)
        case r: RDefined[B] =>
          goR(r) match
            case None => (None, AllDone)
            case some => (some, followUp)
        case l: LDefined[B] =>
          (Some(BiDef(l, newContentR)), followUp)
        case BiDef(l, r) =>
          goR(r) match
            case Some(r) => (Some(BiDef(l, r)), followUp)
            case None    => (None, AllDone)
        case Slated(l, r) =>
          // proceed anyway, since the current contraction is higher priority
          // and has already obstructed whatever action marked this cell as slated
          goR(r) match
            case Some(r) => (Some(BiDef(l, r)), followUp)
            case None    => (None, AllDone)
        case Consumed() =>
          (None, AllDone)
      }
  }

  def initLFwdRInvSrcContraction[A, B]: (CellContent[B], ContractLFwdRInvSrc[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (invTgtContent, contraction) =>
      val ContractLFwdRInvSrc(lCell, slatedInvSrc, inv, invTgt) = contraction

      def goR(r: RDefined[B]): Option[RDefined[B]] = {
        def goInvSrc[X](src: Cell[X], inv1: Inversion[X, B]): Option[RDefined[B]] = {
          assert(inv1 == inv, s"Unexpected inversion $inv1, expected $inv")
          if (src eq slatedInvSrc)
            Some(RSkippingUpLeft(newTgt = lCell, slatedInvSrc, inv))
          else
            None
        }

        r match {
          case RInvertTgt(src, inv1) =>
            goInvSrc(src, inv1)
          case RSkippingUpLeft(newSrc, oldSrc, inv1) =>
            goInvSrc(newSrc, inv1)
          case r: RComplete[B] =>
            None
        }
      }

      def followUp: ActionResult =
        SkipToRInvTgt(contraction)

      invTgtContent match {
        case Empty() =>
          ( Some(RSkippingUpLeft(newTgt = lCell, oldTgt = slatedInvSrc, inv))
          , followUp
          )
        case r: RDefined[B] =>
          goR(r) match
            case None => (None, AllDone)
            case some => (some, followUp)
        case BiDef(l, r) =>
          goR(r) match
            case Some(r) => (Some(BiDef(l, r)), followUp)
            case None    => (None, AllDone)
        case Slated(_, _) =>
          // obstructed, as we consider inversion target to be higher priority than inversion source
          (None, AllDone)
        case PropagatingRCompletion(_, _) | PropagatingLCompletion(_, _) | Consumed() => // overtaken
          (None, AllDone)
      }
  }

  def initContractionLInvSrcRFwdClaimTgt[A, B]: (CellContent[A], ContractLInvSrcRFwd[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (invTgtContent, contraction) =>
      val ContractLInvSrcRFwd(self, lInv, slated, rCell) = contraction

      def newContentL = LInvertTgtClaimed(slated, lInv)
      def followUp    = ContractionLInvSrcRFwdClaimedTgt(contraction)

      def lStillCurrent(l: LDefined[A]): Boolean =
        l match {
          case LInvertTgt(src, _)         => slated eq src
          case LInvertTgtClaimed(src, _)  => slated eq src
          case LSkippingLeftUp(src, _, _) => slated eq src
          case LSkippingUpUp(_, _, _, _)  => false
          case LInvertSrc(_, _)           => false
          case l: LComplete[A]            => false
        }

      invTgtContent match {
        case Empty() =>
          (Some(newContentL), followUp)
        case l: LDefined[A] =>
          if (lStillCurrent(l)) (Some(newContentL), followUp)
          else                  (None, AllDone)
        case BiDef(l, r) =>
          if (lStillCurrent(l)) (Some(BiDef(newContentL, r)), followUp)
          else                  (None, AllDone)
        case Slated(_, _) => // obstructed
          (None, AllDone)
        case PropagatingRCompletion(_, _) | Consumed() => // overtaken
          (None, AllDone)
      }
  }

  def initContractionLInvSrcRFwdAfterTgtClaimed[A, B]: (CellContent[B], ContractLInvSrcRFwd[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (rContent, contraction) =>
      val ContractLInvSrcRFwd(invTgt, lInv, slated, self) = contraction

      def newContentL = LSkippingLeftDown(invTgt, lInv, oldTgt = slated)
      def followUp    = LSkipUpRight(contraction)

      def goL(l: LDefined[B]): Option[LDefined[B]] =
        l match {
          case LFwd(lTgt) =>
            if (lTgt eq slated) Some(newContentL)
            else                None
          case LSkippingLeftLeft(newTgt, _) =>
            if (newTgt eq slated) Some(newContentL)
            else                  None
          case LSkippingUpUp(lTgt, _, _, _) =>
            if (lTgt eq slated) Some(newContentL)
            else                None
        }

      rContent match {
        case Empty() =>
          (Some(newContentL), followUp)
        case l: LDefined[B] =>
          goL(l) match
            case None => (None, AllDone)
            case some => (some, followUp)
        case BiDef(l, r) =>
          goL(l) match
            case Some(l) => (Some(BiDef(l, r)), followUp)
            case None    => (None, AllDone)
        case Slated(_, _) => // obstructed
          (None, AllDone)
        case PropagatingRCompletion(_, _) | Consumed() => // overtaken
          (None, AllDone)
      }
  }

  def initContractionLInvTgtRFwd[A, B]: (CellContent[B], ContractLInvTgtRFwd[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (rContent, contraction) =>
      val ContractLInvTgtRFwd(invSrc, lInv, slatedInvTgt, self) = contraction

      def newContentL = LSkippingLeftUp(invSrc, lInv, oldTgt = slatedInvTgt)
      def followUp    = LSkipDownRight(contraction)

      def lStillCurrent(l: LDefined[B]): Boolean =
        l match {
          case LFwd(tgt)                      => tgt eq slatedInvTgt
          case LSkippingLeftLeft(newTgt, _)   => newTgt eq slatedInvTgt
          case LSkippingUpUp(newTgt, _, _, _) => newTgt eq slatedInvTgt
          case DoneSupplied                   => false
        }

      rContent match {
        case l: LDefined[B] =>
          if (lStillCurrent(l)) (Some(newContentL), followUp)
          else                  (None, AllDone)
        case BiDef(l, r) =>
          if (lStillCurrent(l)) (Some(BiDef(newContentL, r)), followUp)
          else                  (None, AllDone)
        case Slated(_, _) => // obstructed
          (None, AllDone)
        case PropagatingRCompletion(_, _) | Consumed() => // overtaken
          (None, AllDone)
      }
  }

  def initContractionLInvSrcRInvTgt[A, B]: (CellContent[A], ContractLInvSrcRInvTgt[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (tgtContent, contraction) =>
      val ContractLInvSrcRInvTgt(src, rInv, slated, lInv, self) = contraction

      def newContentL = LSkippingUpUp(src, rInv, slated, lInv)
      def followUp    = RSkipDownDown(contraction)

      def lStillCurrent(l: LDefined[A]): Boolean =
        l match {
          case LInvertTgt(src0, _)         => slated eq src0
          case LInvertTgtClaimed(src0, _)  => slated eq src0
          case LSkippingLeftUp(src0, _, _) => slated eq src0
          case DoneSupplied                => false
          case PingSupplied                => false
        }

      tgtContent match {
        case BiDef(l, r) =>
          if (lStillCurrent(l)) (Some(BiDef(newContentL, r)), followUp)
          else                  (None, AllDone)
        case l: LDefined[A] =>
          if (lStillCurrent(l)) (Some(newContentL), followUp)
          else                  (None, AllDone)
        case Slated(_, _) => // obstructed
          (None, AllDone)
        case Empty() =>
          (Some(newContentL), followUp)
        case PropagatingRCompletion(_, _) | Consumed() => // overtaken
          (None, AllDone)
      }
  }

  def skipAhead[A]: (CellContent[A], ContractBiFwd[A]) => (Option[CellContent[A]], ActionResult) = {
    (lContent, contraction) =>
      val ContractBiFwd(lCell, mCell, rCell) = contraction

      def goCombine(l: LDefined[A], r: RDefined[A]): (Option[CellContent[A]], ActionResult) = {
        val (content, res) = combine(lCell, l, r)
        val action = res.takeUp(CompleteBiFwdContraction(contraction))
        (Some(content), action and ConsumeSlatedCell(lCell, mCell, rCell))
      }

      def goBi(l: LDefined[A], r: RDefined[A]): (Option[CellContent[A]], ActionResult) = {
        r match {
          case RFwd(tgt) =>
            if (tgt eq mCell)
              goCombine(l, RFwd(rCell))
            else // overtaken
              (None, AllDone)
        }
      }

      lContent match {
        case RFwd(tgt) =>
          if (tgt eq mCell)
            (Some(RFwd(rCell)), CompleteBiFwdContraction(contraction) and ConsumeSlatedCell(lCell, mCell, rCell))
          else // overtaken
            (None, AllDone)
        case BiDef(l, r) =>
          goBi(l, r)
        case Slated(l, r) =>
          goBi(l, r)
        case l: LDefined[A] =>
          goCombine(l, RFwd(rCell))
        case Empty() =>
          (Some(RFwd(rCell)), CompleteBiFwdContraction(contraction) and ConsumeSlatedCell(lCell, mCell, rCell))
        case PropagatingLCompletion(_, _) | Consumed() => // overtaken
          (None, AllDone)
      }
  }

  def skipToRInvSrc[A, B]: (CellContent[A], ContractLFwdRInvTgt[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (lContent, contraction) =>
      val ContractLFwdRInvTgt(lCell, slatedCell, inversion, invSrc) = contraction

      def newContentR =
        RInvertTgt(invSrc, inversion)
      def followUp =
        CompleteLFwdRInvTgtContraction(contraction) and
        ConsumeSlatedCell(lCell, slatedCell, invSrc)

      def goR(r: RDefined[A]): Option[RDefined[A]] =
        r match {
          case RFwd(rTgt) =>
            if (rTgt eq slatedCell)
              Some(newContentR)
            else // overtaken
              None
        }

      def goCombine(l: LDefined[A], r: RDefined[A]): (Option[CellContent[A]], ActionResult) =
        val (content, res) = combine(lCell, l, r)
        val action = res.takeUp(CompleteLFwdRInvTgtContraction(contraction))
        (Some(content), action and ConsumeSlatedCell(lCell, slatedCell, invSrc))

      lContent match {
        case Empty() =>
          (Some(newContentR), followUp)
        case r: RDefined[A] =>
          goR(r) match
            case None => (None, AllDone)
            case some => (some, followUp)
        case BiDef(l, r) =>
          goR(r) match
            case Some(r) => (Some(BiDef(l, r)), followUp)
            case None    => (None, AllDone)
        case l: LDefined[A] =>
          goCombine(l, newContentR)
        case Slated(l, r) =>
          goR(r) match
            case Some(r) => goCombine(l, r)
            case None    => (None, AllDone)
        case Consumed() =>
          (None, AllDone)
      }
  }

  def skipToRInvTgt[A, B]: (CellContent[A], ContractLFwdRInvSrc[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (lContent, contraction) =>
      val ContractLFwdRInvSrc(lCell, slatedCell, inversion, invTgt) = contraction

      def goR(r: RDefined[A]): Option[RDefined[A]] =
        r match {
          case RFwd(rTgt) =>
            if (rTgt eq slatedCell)
              Some(RInvertSrc(inversion, invTgt))
            else // overtaken
              None
        }

      def goCombine(l: LDefined[A], r: RDefined[A]): (Option[CellContent[A]], ActionResult) =
        val (content, res) = combine(lCell, l, r)
        val action = res.takeUp(CompleteLFwdRInvSrcContraction(contraction))
        (Some(content), action and ConsumeSlatedCell(lCell, slatedCell, invTgt))

      def followUp =
        CompleteLFwdRInvSrcContraction(contraction) and
        ConsumeSlatedCell(lCell, slatedCell, invTgt)

      lContent match {
        case Empty() =>
          (Some(RInvertSrc(inversion, invTgt)), followUp)
        case r: RDefined[A] =>
          goR(r) match
            case None => (None, AllDone)
            case some => (some, followUp)
        case BiDef(l, r) =>
          goR(r) match
            case Some(r) => goCombine(l, r)
            case None    => (None, AllDone)
        case Slated(l, r) =>
          // proceed anyway, since the current contraction on the right is higher priority
          // and has already obstructed whatever action slated this cell
          goR(r) match
            case Some(r) => goCombine(l, r)
            case None    => (None, AllDone)
        case l: LDefined[A] =>
          goCombine(l, RInvertSrc(inversion, invTgt))
        case Consumed() =>
          (None, AllDone)
      }
  }

  def lSkipUpRight[A, B]: (CellContent[A], ContractLInvSrcRFwd[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (invTgtContent, contraction) =>
      val ContractLInvSrcRFwd(self, lInv, slated, rCell) = contraction

      def newContentL   = LInvertTgt(rCell, lInv)
      def complete      = CompleteLInvSrcRFwdContraction(contraction)
      def consumeSlated = ConsumeSlatedCell(self, slated, rCell)
      def followUp      = complete and consumeSlated

      def checkL(l: LDefined[A]): Unit =
        l match {
          case LInvertTgtClaimed(src, i) =>
            assert(slated eq src, s"Unexpected l-inversion source ${addr(slated)}, expected ${addr(src)}")
            assert(lInv == i, s"Unexpected inversion $lInv, expected $i")
        }

      invTgtContent match {
        case l: LDefined[A] =>
          checkL(l)
          (Some(newContentL), followUp)
        case BiDef(l, r) =>
          checkL(l)
          val (content, res) = combine(self, newContentL, r)
          val action = res.takeUp(complete)
          (Some(content), action and consumeSlated)
        case Empty() =>
          (Some(newContentL), followUp)
      }
  }

  def lSkipDownRight[A, B]: (CellContent[A], ContractLInvTgtRFwd[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (invSrcContent, contraction) =>
      val ContractLInvTgtRFwd(self, lInv, slated, rCell) = contraction

      def newContentL    = LInvertSrc(lInv, rCell)
      def completeAction = CompleteLInvTgtRFwdContraction(contraction)
      def consumeSlated  = ConsumeSlatedCell(self, slated, rCell)
      def followUp       = completeAction and consumeSlated

      def goL(l: LDefined[A]): Option[LDefined[A]] =
        l match {
          case LInvertSrc(i, tgt) =>
            if (slated eq tgt)
              assert(lInv == i, s"Unexpected inversion $lInv, expected $i")
              Some(newContentL)
            else
              None
          case LSkippingLeftDown(tgt, i, _) =>
            if (slated eq tgt)
              assert(lInv == i, s"Unexpected inversion $lInv, expected $i")
              Some(newContentL)
            else
              None
        }

      def goCombine(l: LDefined[A], r: RDefined[A]): (Option[CellContent[A]], ActionResult) = {
        val (content, res) = combine(self, l, r)
        val action = res.takeUp(completeAction)
        (Some(content), action and consumeSlated)
      }

      invSrcContent match
        case BiDef(l, r) =>
          goL(l) match
            case Some(l) => goCombine(l, r)
            case None    => (None, AllDone)
        case Slated(l, r) =>
          goL(l) match
            case None     => (None, AllDone)
            case Some(l) =>
              // proceed, since the action that marked the cell slated was already obstructed by this contraction
              goCombine(l, r)
        case r: RDefined[A] =>
          goCombine(newContentL, r)
        case l: LDefined[A] =>
          goL(l) match
            case None => (None, AllDone)
            case some => (some, followUp)
        case Empty() =>
          (Some(newContentL), followUp)
        case Consumed() =>
          (None, AllDone)
  }

  def rSkipDownDown[A, B]: (CellContent[A], ContractLInvSrcRInvTgt[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (invSrcContent, contraction) =>
      val ContractLInvSrcRInvTgt(self, rInv, slated, lInv, tgt) = contraction

      def newContentR         = RFwd(tgt)
      def completeContraction = CompleteLInvSrcRInvTgtContraction(contraction)
      def consumeSlated       = ConsumeSlatedCell(tgt, slated, self)
      def followUp            = completeContraction and consumeSlated

      def checkR(r: RDefined[A]): Unit =
        r match {
          case RInvertSrc(i, tgt0) =>
            assert(slated eq tgt0, s"Unexpected r-inversion target ${addr(slated)}, expected ${addr(tgt0)}")
            assert(rInv == i)
          case RSkippingDownLeft(i, oldTgt, newTgt) =>
            assert(slated eq newTgt, s"Unexpected r-inversion target ${addr(slated)}, expected ${addr(newTgt)}")
            assert(rInv == i)
        }

      def goCombine(l: LDefined[A], r: RDefined[A]): (Option[CellContent[A]], ActionResult) = {
        val (content, res) = combine(self, l, r)
        val action = res.takeUp(completeContraction)
        (Some(content), action and consumeSlated)
      }

      invSrcContent match {
        case Slated(l, r) =>
          checkR(r)
          goCombine(l, newContentR)
        case BiDef(l, r) =>
          checkR(r)
          goCombine(l, newContentR)
        case l: LDefined[A] =>
          goCombine(l, newContentR)
        case r: RDefined[A] =>
          checkR(r)
          (Some(newContentR), followUp)
        case Empty() =>
          (Some(newContentR), followUp)
        case Consumed() =>
          (None, AllDone)
      }
  }

  def completeBiFwdContraction[A]: (CellContent[A], ContractBiFwd[A]) => (Option[CellContent[A]], ActionResult) = {
    (rContent, contraction) =>
      val ContractBiFwd(lCell, mCell, rCell) = contraction

      def newContentL = LFwd(lCell)

      def goL(l: LDefined[A]): Option[LDefined[A]] =
        l match {
          case LSkippingLeftLeft(newTgt, _) =>
            if (newTgt eq lCell)
              Some(newContentL)
            else // overtaken
              None
          case _ => // overtaken
            None
        }

      rContent match {
        case l: LDefined[A] =>
          (goL(l), AllDone)
        case BiDef(l, r) =>
          goL(l) match
            case Some(l) =>
              val (newContent, res) = combine(rCell, l, r)
              (Some(newContent), res)
            case None =>
              (None, AllDone)
        case Slated(_, _) | PropagatingRCompletion(_, _) | PropagatingLCompletion(_, _) | Consumed() => // overtaken
          (None, AllDone)
      }
  }

  def completeLFwdRInvTgtContraction[A, B]: (CellContent[B], ContractLFwdRInvTgt[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (invSrcContent, contraction) =>
      val ContractLFwdRInvTgt(lCell, slatedCell, inv, self) = contraction

      def rStillCurrent(r: RDefined[B]): Boolean =
        r match {
          case RSkippingDownLeft(rInv, _, newTgt) => newTgt eq lCell
          case RInvertSrc(_, _) | RFwd(_)         => false
          case _: RComplete[B]                    => false
        }

      def newContentR = RInvertSrc(inv, lCell)

      invSrcContent match {
        case r: RDefined[B] =>
          if (rStillCurrent(r)) (Some(newContentR), AllDone)
          else                  (None, AllDone)
        case BiDef(l, r) =>
          if (rStillCurrent(r))
            val (content, action) = combine(self, l, newContentR)
            (Some(content), action)
          else
            (None, AllDone)
        case Slated(_, _) => // overtaken
          (None, AllDone)
        case Consumed() =>
          (None, AllDone)
      }
  }

  def completeLFwdRInvSrcContraction[A, B]: (CellContent[B], ContractLFwdRInvSrc[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (invTgtContent, contraction) =>
      val ContractLFwdRInvSrc(lCell, bypassedCell, i, self) = contraction

      def goR(r: RDefined[B]): Option[RDefined[B]] = {
        r match {
          case RSkippingUpLeft(newTgt, _, rInv) =>
            if (newTgt eq lCell) Some(RInvertTgt(newTgt, rInv))
            else                 None
          case RInvertTgt(_, _) => // overtaken
            None
        }
      }

      invTgtContent match {
        case r: RDefined[B] =>
          (goR(r), AllDone)
        case BiDef(l, r) =>
          goR(r) match
            case Some(r) =>
              val (content, res) = combine(self, l, r)
              (Some(content), res)
            case None =>
              (None, AllDone)
        case PropagatingLCompletion(_, _) | PropagatingRCompletion(_, _) | Consumed() => // overtaken
          (None, AllDone)
      }
  }

  def completeLInvSrcRFwdContraction[A, B]: (CellContent[B], ContractLInvSrcRFwd[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (rContent, contraction) =>
      val ContractLInvSrcRFwd(tgt, lInv, slated, rCell) = contraction

      def goL(l: LDefined[B]): Option[LDefined[B]] =
        l match {
          case LSkippingLeftDown(tgt0, lInv0, _) =>
            if (tgt eq tgt0)
              assert(lInv == lInv0, s"Unexpected inversion $lInv, expected $lInv0")
              Some(LInvertSrc(lInv, tgt))
            else // overtaken
              None
          case _ =>
            None
        }

      rContent match {
        case l: LDefined[B] =>
          (goL(l), AllDone)
        case BiDef(l, r) =>
          goL(l) match
            case Some(l) =>
              val (content, res) = combine(rCell, l, r)
              (Some(content), res)
            case None =>
              (None, AllDone)
        case Slated(_, _) =>
          (None, AllDone)
        case Consumed() =>
          (None, AllDone)
      }
  }

  def completeLInvTgtRFwdContraction[A, B]: (CellContent[B], ContractLInvTgtRFwd[A, B]) => (Option[CellContent[B]], ActionResult) = {
    (rContent, contraction) =>
      val ContractLInvTgtRFwd(src, lInv, slated, rCell) = contraction

      def goL(l: LDefined[B]): Option[LDefined[B]] =
        l match {
          case LSkippingLeftUp(src0, lInv0, _) =>
            if (src eq src0)
              assert(lInv == lInv0, s"Unexpected inversion $lInv, expected $lInv0")
              Some(LInvertTgt(src, lInv))
            else // overtaken
              None
          case LInvertTgtClaimed(_, _) | LSkippingUpUp(_, _, _, _) =>
            None
          case _: LComplete[B] =>
            None
        }

      rContent match {
        case l: LDefined[B] =>
          (goL(l), AllDone)
        case BiDef(l, r) =>
          goL(l) match
            case Some(l) =>
              val (content, res) = combine(rCell, l, r)
              (Some(content), res)
            case None =>
              (None, AllDone)
        case PropagatingRCompletion(_, _) | PropagatingLCompletion(_, _) | Consumed() =>
          (None, AllDone)
      }
  }

  def completeLInvSrcRInvTgtContraction[A, B]: (CellContent[A], ContractLInvSrcRInvTgt[A, B]) => (Option[CellContent[A]], ActionResult) = {
    (tgtContent, contraction) =>
      val ContractLInvSrcRInvTgt(src, rInv, slated, lInv, self) = contraction

      def lStillCurrent(l: LDefined[A]): Boolean =
        l match
          case LSkippingUpUp(src0, rInv0, oldSrc, lInv0) =>
            if (src eq src0)
              assert(rInv == rInv0)
              assert(slated eq oldSrc)
              assert(lInv == lInv0)
              true
            else
              false
          case _ =>
            false

      def newContentL = LFwd(src)

      tgtContent match {
        case l: LDefined[A] =>
          if (lStillCurrent(l)) (Some(newContentL), AllDone)
          else                  (None, AllDone)
        case BiDef(l, r) =>
          if (lStillCurrent(l))
            val (content, res) = combine(self, newContentL, r)
            (Some(content), res)
          else
            (None, AllDone)
        case Slated(l, r) =>
          assert(!lStillCurrent(l))
          (None, AllDone)
        case PropagatingLCompletion(_, _) | PropagatingRCompletion(_, _) | Consumed() =>
          (None, AllDone)
      }
  }

  def consumeSlatedCell[A, B, C]: (CellContent[B], ConsumeSlatedCell[A, B, C]) => (Option[CellContent[B]], ActionResult) = {
    (mContent, cells) =>
      val ConsumeSlatedCell(lCell, mCell, rCell) = cells
      mContent match {
        case Slated(l, r) =>
          // check that `l` still points to `lCell`
          l match {
            case LFwd(`lCell`) =>
            case LRole(`lCell`, _) =>
            case LInvertTgt(`lCell`, _) =>
            case LInvertSrc(_, `lCell`) =>
          }
          // check that `r` still points to `rCell`
          r match {
            case RFwd(`rCell`) =>
            case RRole(_, `rCell`) =>
            case RInvertTgt(`rCell`, _) =>
            case RInvertSrc(_, `rCell`) =>
            case JoinNeed1(`rCell`) =>
            case JoinNeed2(`rCell`) =>
            case JoinPong1(`rCell`) =>
            case JoinPong2(`rCell`) =>
          }
          (Some(Consumed()), AllDone)
      }
  }

  def mapVal[A, B]: (CellContent[Val[A]], (Cell[Val[A]], A => B, Cell[Val[B]])) => (CellContent[Val[A]], ActionResult) = {
    (srcContent, payload) =>
      val (self, f, tgt) = payload

      def newContentR = RMapValSrc(f, tgt)
      def nextStep    = LExpectVal(self, tgt)

      srcContent match {
        case Empty() =>
          (newContentR, nextStep)
        case ValSupplied(a) =>
          (Consumed(), MapValTriggered(self, a, f, tgt))
        case l: LDefined[Val[A]] =>
          (BiDef(l, newContentR), nextStep)
      }
  }

  def lExpectVal[A, B]: (CellContent[Val[B]], LExpectVal[A, B]) => (Option[CellContent[Val[B]]], ActionResult) = {
    (tgtContent, payload) =>
      val LExpectVal(src, self) = payload

      def newContentL = LValTgt[A, B](src)

      tgtContent match {
        case Empty() =>
          (Some(newContentL), AllDone)
        case r: RDefined[Val[B]] =>
          (Some(BiDef(newContentL, r)), AllDone)
        case Consumed() =>
          (None, AllDone)
      }
  }

  def lExpectDone[A]: (CellContent[Done], LExpectDone[A]) => (CellContent[Done], ActionResult) = {
    (tgtContent, payload) =>
      val LExpectDone(src, self) = payload

      def newContentL = LDoneTgt[A](src)

      tgtContent match {
        case Empty() =>
          (newContentL, AllDone)
        case r: RDefined[Done] =>
          (BiDef(newContentL, r), AllDone)
      }
  }

  def constVal[A]: (CellContent[Done], (Cell[Done], A, Cell[Val[A]])) => (CellContent[Done], ActionResult) = {
    (srcContent, payload) =>
      val (self, value, tgt) = payload

      def newContentR = RConstVal(value, tgt)
      def nextStep    = LExpectVal(self, tgt)

      srcContent match {
        case Empty() =>
          (newContentR, nextStep)
        case l: LComplete[Done] =>
          val (content, action) = combineLCompleteRDefined(self, l, newContentR)
          (content, action takeUp nextStep)
        case l: LDefined[Done] =>
          (BiDef(l, newContentR), nextStep)
      }
  }

  def neglect[A]: (CellContent[Val[A]], (Cell[Val[A]], Cell[Done])) => (CellContent[Val[A]], ActionResult) = {
    (srcContent, cells) =>
      val (self, tgt) = cells

      def newContentR = RNeglectVal[A](tgt)
      def nextStep    = LExpectDone(self, tgt)

      srcContent match {
        case Empty() =>
          (newContentR, nextStep)
        case l: LComplete[Val[A]] =>
          val (content, action) = combineLCompleteRDefined(self, l, newContentR)
          (content, action takeUp nextStep)
        case l: LDefined[Val[A]] =>
          (BiDef(l, newContentR), nextStep)
      }
  }

  def splitVal[A, B]: (CellContent[Val[(A, B)]], (Cell[Val[(A, B)]], Cell[Val[A]], Cell[Val[B]])) => (CellContent[Val[(A, B)]], ActionResult) = {
    (srcContent, cells) =>
      val (self, tgt1, tgt2) = cells

      def newContentR = RSplitVal(tgt1, tgt2)
      def nextStep    = FillRoleL(self, RoleL.SplitVal1(), tgt1) and FillRoleL(self, RoleL.SplitVal2(), tgt2)

      srcContent match {
        case Empty() =>
          (newContentR, nextStep)
      }
  }

  def zipVal[A, B]: (CellContent[Val[(A, B)]], (Cell[Val[A]], Cell[Val[B]], Cell[Val[(A, B)]])) => (CellContent[Val[(A, B)]], ActionResult) = {
    (tgtContent, cells) =>
      val (src1, src2, self) = cells

      def newContentL = LZipVal(src1, src2)
      def nextStep    = FillRoleR(src1, RoleR.ZipVal1(), self) and FillRoleR(src2, RoleR.ZipVal2(), self)

      tgtContent match {
        case Empty() =>
          (newContentL, nextStep)
        case r: RDefined[Val[(A, B)]] =>
          (BiDef(newContentL, r), nextStep)
      }
  }

  def liftEither[A, B]: (CellContent[Val[Either[A, B]]], (Cell[Val[Either[A, B]]], Cell[Val[A] |+| Val[B]])) => (CellContent[Val[Either[A, B]]], ActionResult) = {
    (srcContent, payload) =>
      val (self, tgt) = payload

      def newContentR = RLiftEither(tgt)
      def nextStep    = LReciprocateLiftEither(self, tgt)

      srcContent match {
        case Empty() =>
          (newContentR, nextStep)
        case ValSupplied(v) =>
          val l1: LComplete[Val[A] |+| Val[B]] = v match
            case Left(a)  => InjectedL(Cell(ValSupplied(a)))
            case Right(b) => InjectedR(Cell(ValSupplied(b)))
          (Consumed(), PropagateLCompletionRight(self, l1, tgt))
        case l: LDefined[Val[Either[A, B]]] =>
          (BiDef(l, newContentR), nextStep)
      }
  }

  def lReciprocateLiftEither[A, B]: (CellContent[Val[A] |+| Val[B]], LReciprocateLiftEither[A, B]) => (Option[CellContent[Val[A] |+| Val[B]]], ActionResult) = {
    (tgtContent, payload) =>
      val LReciprocateLiftEither(src, self) = payload

      def newContentL = LLiftedEither[A, B](src)

      tgtContent match {
        case Empty() =>
          (Some(newContentL), AllDone)
        case r: EitherSwitch[Val[A], Val[B], c] =>
          (Some(BiDef(newContentL, r)), AllDone)
        case Consumed() =>
          (None, AllDone)
      }
  }

  def awaitDone(
    content: CellContent[Done],
    cellAndListener: (Cell[Done], Either[Throwable, Unit] => Unit),
  ): (CellContent[Done], ActionResult) = {
    val (self, listener) = cellAndListener
    content match
      case Empty() =>
        (DoneCallback(listener), AllDone)
      case l: JoinOf =>
        (BiDef(l, DoneCallback(listener)), AllDone)
      case l: Join1 =>
        (BiDef(l, DoneCallback(listener)), AllDone)
      case l: Join2 =>
        (BiDef(l, DoneCallback(listener)), AllDone)
      case l @ LFwd(lTgt) =>
        val payload = DoneCallback(listener)
        (PropagatingRCompletion(l, payload), PropagateRCompletionLeft(lTgt, payload, self))
      case l: LSkippingLeftLeft[Done] =>
        (BiDef(l, DoneCallback(listener)), AllDone)
      case l: LSkippingLeftUp[x, Done] =>
        (BiDef(l, DoneCallback(listener)), AllDone)
      case l: LSkippingUpUp[Done, x] =>
        (BiDef(l, DoneCallback(listener)), AllDone)
      case l @ LInvertTgt(src, i) =>
        val r = DoneCallback(listener)
        (PropagatingRCompletion(l, r), PropagateRCompletionUp(src, r.lInvert(i), i, self))
      case l @ LInvertTgtClaimed(src, i) =>
        val r = DoneCallback(listener)
        (PropagatingRCompletion(l, r), PropagateRCompletionUp(src, r.lInvert(i), i, self))
      case DoneSupplied =>
        (Consumed(), CallbackTriggered(listener, Right(())))
  }

  def awaitEither[A, B](
    eitherContent: CellContent[A |+| B],
    cellAndListener: (Cell[A |+| B], Either[Throwable, Either[Cell[A], Cell[B]]] => Unit),
  ): (CellContent[A |+| B], ActionResult) = {
    val (self, listener) = cellAndListener
    eitherContent match {
      case Empty() =>
        (EitherCallback(listener), AllDone)
      case InjectedL(cell) =>
        (Consumed(), CallbackTriggered(listener, Right(Left(cell))))
      case InjectedR(cell) =>
        (Consumed(), CallbackTriggered(listener, Right(Right(cell))))
      case l @ LFwd(lTgt) =>
        val payload = EitherCallback(listener)
        (PropagatingRCompletion(l, payload), PropagateRCompletionLeft(lTgt, payload, self))
      case EitherCallback(_) | Consumed() =>
        throw new IllegalStateException("Double observer")
    }
  }

  def crashFromLeft[A, B]: (CellContent[B], (Cell[A], Throwable, Cell[B])) => (Option[CellContent[B]], ActionResult) = {
    (tgtContent, payload) =>
      val (origin, e, self) = payload

      def newContentL = LCrashed[B](e)

      tgtContent match {
        case Empty() =>
          (Some(newContentL), AllDone)
      }
  }

  private def addr[X](c: Cell[X]): String =
    "@" + System.identityHashCode(c).toHexString
}

/** Role an `A`-cell plays in a `B`-cell to its right. */
enum RoleR[A, B] {
  case Joiner1 extends RoleR[Done, Done]
  case Joiner2 extends RoleR[Done, Done]
  case NeedNotification extends RoleR[Pong, Need]
  case NotifyNeedTgt extends RoleR[Need, Need]
  case ChoiceNotification[A, B]() extends RoleR[Pong, A |&| B]
  case NotifyChoiceTgt[A, B]() extends RoleR[A |&| B, A |&| B]
  case StrengthenPingSrc extends RoleR[Ping, Done]
  case InjectionTrigger[A, B]() extends RoleR[Ping, A |+| B]
  case ZipVal1[A, B]() extends RoleR[Val[A], Val[(A, B)]]
  case ZipVal2[A, B]() extends RoleR[Val[B], Val[(A, B)]]
}

/** Role a `B`-cell plays in an `A`-cell to its left. */
enum RoleL[A, B] {
  case JoinerNeed1 extends RoleL[Need, Need]
  case JoinerNeed2 extends RoleL[Need, Need]
  case JoinerPong1 extends RoleL[Pong, Pong]
  case JoinerPong2 extends RoleL[Pong, Pong]
  case SelectContestant1 extends RoleL[One |&| One, Pong]
  case SelectContestant2 extends RoleL[One |&| One, Pong]
  case DoneNotification extends RoleL[Done, Ping]
  case NotifyDoneTgt extends RoleL[Done, Done]
  case EitherNotification[A, B]() extends RoleL[A |+| B, Ping]
  case NotifyEitherTgt[A, B]() extends RoleL[A |+| B, A |+| B]
  case SplitVal1[A, B]() extends RoleL[Val[(A, B)], Val[A]]
  case SplitVal2[A, B]() extends RoleL[Val[(A, B)], Val[B]]
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

  def fromPair[X, Y](using ev: A =:= (X |*| Y)): B =:= -[X |*| Y] =
    this match
      case Universal() => ev.liftCo[-]
      case DoneNeed    => throw AssertionError("Done =:= (X |*| Y)")
      case PingPong    => throw AssertionError("Ping =:= (X |*| Y)")

  def toInvPair[X, Y](using ev: B =:= -[X |*| Y]): A =:= (X |*| Y) = {
    def go(i: Inversion[A, -[X |*| Y]]): A =:= (X |*| Y) =
      i match
        case Inversion.Universal() => summon[A =:= (X |*| Y)]
        // case Inversion.DoneNeed    => throw AssertionError("Need =:= -[X |*| Y]")
        // case Inversion.PingPong    => throw AssertionError("Pong =:= -[X |*| Y]")

    go(ev.substituteCo(this))
  }
}
