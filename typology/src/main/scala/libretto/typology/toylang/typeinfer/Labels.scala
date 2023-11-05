package libretto.typology.toylang.typeinfer

import libretto.lambda.util.SourcePos
import libretto.scaletto.StarterKit._

import java.util.concurrent.atomic.AtomicInteger

class Labels[V](using V: Ordering[V]) {
  enum Lbl:
    case Base(value: V, counter: AtomicInteger)
    case Clone(base: Lbl, tag: Int)
    case Abstracted(base: TParamLbl, counter: AtomicInteger)
    import Lbl.Basal
    def basal: Basal =
      this match
        case Clone(base, _) => base.basal
        case x: Base        => x
        case x: Abstracted  => x
    def mkClone(): Lbl =
      this match
        case b @ Base(_, counter)       => Clone(b, counter.incrementAndGet())
        case b @ Abstracted(_, counter) => Clone(b, counter.incrementAndGet())
        case Clone(base, _)             => base.mkClone()
    def declone: (Basal, List[Int]) =
      def go(lbl: Lbl, acc: List[Int]): (Basal, List[Int]) =
        lbl match
          case Clone(base, tag) => go(base, tag :: acc)
          case x: Base          => (x, acc)
          case x: Abstracted    => (x, acc)
      go(this, Nil)
    def originalBase: V =
      this match
        case Base(value, _) => value
        case Clone(base, tag) => base.originalBase
        case Abstracted(TParamLbl.Promoted(base), _) => base.originalBase
    override def toString =
      this match
        case Abstracted(base, _) => s"$base+"
        case Base(value, _) => s"{$value}"
        case Clone(base, tag) => s"$base.$tag"
  end Lbl
  enum TParamLbl:
    case Promoted(base: Lbl)
    override def toString =
      this match
        case Promoted(base) => s"[$base]"
  end TParamLbl
  object Lbl:
    type Basal = Base | Abstracted
    def compareBasal(a: Basal, b: Basal): Either[Basal, Either[Basal, Basal]] =
      (a, b) match
        case (Base(x, _), Base(y, _)) =>
          V.compare(x, y) match {
            case 0 => Left(a)
            case i if i < 0 => Right(Left (a))
            case i if i > 0 => Right(Right(b))
          }
        case (Base(_, _), Abstracted(_, _)) =>
          Right(Left(a))
        case (Abstracted(_, _), Base(_, _)) =>
          Right(Right(b))
        case (Abstracted(x, _), Abstracted(y, _)) =>
          TParamLbl.compareStrict(x, y) match
            case Left(z)         => Left(a)
            case Right(Left(_))  => Right(Left(a))
            case Right(Right(_)) => Right(Right(b))
    def compareLax(a: Lbl, b: Lbl): Either[Lbl, Either[Lbl, Lbl]] =
      compareBasal(a.basal, b.basal) match
        case Left(_) => Left(a)
        case Right(Left(_))  => Right(Left(a))
        case Right(Right(_)) => Right(Right(b))
    def compareStrict(a: Lbl, b: Lbl): Either[Lbl, Either[Lbl, Lbl]] =
      val (x, xTags) = a.declone
      val (y, yTags) = b.declone
      compareBasal(x, y) match
        case Left(_) =>
          compareLists(xTags, yTags) match
            case 0 => Left(a)
            case i if i < 0 => Right(Left(a))
            case i if i > 0 => Right(Right(b))
        case Right(Left(_)) =>
          Right(Left(a))
        case Right(Right(_)) =>
          Right(Right(b))
    private def compareLists[A](as: List[A], bs: List[A])(using A: Ordering[A]): Int =
      (as zip bs)
        .map { case (a, b) => A.compare(a, b) }
        .find(_ != 0) match {
          case Some(i) => i
          case None    => as.size compareTo bs.size
        }
  end Lbl
  object TParamLbl:
    def compareStrict(a: TParamLbl, b: TParamLbl): Either[TParamLbl, Either[TParamLbl, TParamLbl]] =
      (a, b) match
        case (Promoted(x), Promoted(y)) =>
          Lbl.compareStrict(x, y) match
            case Left(z)         => Left(Promoted(z))
            case Right(Left(x))  => Right(Left(Promoted(x)))
            case Right(Right(y)) => Right(Right(Promoted(y)))
  opaque type Label       = Val[Lbl]
  opaque type TParamLabel = Val[TParamLbl]
  def from(v: V): One -⚬ Label =
    const(Lbl.Base(v, AtomicInteger(0)))
  def make(v: V)(using SourcePos, LambdaContext): $[Label] =
    constant(from(v)) > alsoPrintLine(x => s"Creating $x")
  val split: Label -⚬ (Label |*| Label) =
    mapVal { (lbl: Lbl) =>
      val res = (lbl.mkClone(), lbl.mkClone())
      println(s"$lbl split into $res")
      res
    } > liftPair
  val compare: (Label |*| Label) -⚬ (Label |+| (Label |+| Label)) =
    λ { case a |*| b =>
      (a ** b) :>> mapVal { case (a, b) =>
        val res = Lbl.compareLax(a, b)
        println(s"comparing $a and $b resulted in $res")
        res
      } :>> liftEither :>> |+|.rmap(liftEither)
    }
  val neglect: Label -⚬ Done =
    // dsl.neglect
    printLine(x => s"Neglecting $x")
  val neglectTParam: TParamLabel -⚬ Done =
    // dsl.neglect
    printLine(x => s"Neglecting TParam $x")
  val generify: Label -⚬ TParamLabel =
    // mapVal { TParamLbl.Promoted(_) }
    mapVal { x =>
      val res = TParamLbl.Promoted(x)
      println(s"$x generified to $res")
      res
    }
  val abstractify: TParamLabel -⚬ Label =
    // mapVal { Lbl.Abstracted(_) }
    mapVal { x =>
      val res = Lbl.Abstracted(x, AtomicInteger(0))
      println(s"$x abstractified to $res")
      res
    }
  val show: Label -⚬ Val[String] =
    // mapVal(_.toString)
    mapVal(x =>
      val res = x.toString
      println(s"$x converted to string")
      res
    )
  val unwrapOriginal: Label -⚬ Val[V] =
    mapVal(_.originalBase)
  val unwrapOriginalTP: TParamLabel -⚬ Val[V] =
    mapVal { case TParamLbl.Promoted(x) => x.originalBase }
  def alsoDebugPrint(f: String => String): Label -⚬ Label =
    alsoPrintLine(x => f(x.toString))
  def alsoDebugPrintTP(f: String => String): TParamLabel -⚬ TParamLabel =
    alsoPrintLine(x => f(x.toString))
  given Junction.Positive[Label] =
    scalettoLib.junctionVal
  given Junction.Positive[TParamLabel] =
    scalettoLib.junctionVal
}
