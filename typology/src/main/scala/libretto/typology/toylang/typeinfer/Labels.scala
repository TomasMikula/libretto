package libretto.typology.toylang.typeinfer

import libretto.lambda.util.SourcePos
import libretto.scaletto.StarterKit._

import java.util.concurrent.atomic.AtomicInteger
import libretto.scaletto.StarterKit

trait Labels[V] {
  type Label

  type TParamLabel // TODO: is necessary?

  def create(v: V): One -⚬ Label
  def split: Label -⚬ (Label |*| Label)
  def compare: (Label |*| Label) -⚬ (Label |+| (Label |+| Label))
  def neglect: Label -⚬ Done
  def unwrapOriginal: Label -⚬ Val[V]

  given junctionLabel: Junction.Positive[Label]

  def generify: Label -⚬ TParamLabel
  def abstractify: TParamLabel -⚬ Label
  def neglectTParam: TParamLabel -⚬ Done
  val unwrapOriginalTP: TParamLabel -⚬ Val[V]

  given junctionTParamLabel: Junction.Positive[TParamLabel]

  def show: Label -⚬ Val[String]
  def alsoShow: Label -⚬ (Label |*| Val[String])
  def alsoDebugPrint(f: String => String): Label -⚬ Label

  def alsoDebugPrintTP(f: String => String): TParamLabel -⚬ TParamLabel

  trait Nested {
    val labels: Labels[V]

    def promote: labels.TParamLabel -⚬ Label
  }

  def nested: Nested
}

object Labels {
  def apply[V](using Ordering[V]): Labels[V] =
    new LabelsImpl[V]
}

object LabelsImpl {
  enum Lbl[V]:
    case Base(value: V, counter: AtomicInteger)
    case Clone(base: Lbl[V], tag: Int)
    case Abstracted(base: TParamLbl[V], counter: AtomicInteger)
    import Lbl.Basal
    def basal: Basal[V] =
      this match
        case Clone(base, _)    => base.basal
        case x: Base[V]        => x
        case x: Abstracted[V]  => x
    def mkClone(): Lbl[V] =
      this match
        case b @ Base(_, counter)       => Clone(b, counter.incrementAndGet())
        case b @ Abstracted(_, counter) => Clone(b, counter.incrementAndGet())
        case Clone(base, _)             => base.mkClone()
    def declone: (Basal[V], List[Int]) =
      def go(lbl: Lbl[V], acc: List[Int]): (Basal[V], List[Int]) =
        lbl match
          case Clone(base, tag) => go(base, tag :: acc)
          case x: Base[V]       => (x, acc)
          case x: Abstracted[V] => (x, acc)
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

  enum TParamLbl[V]:
    case Promoted(base: Lbl[V])
    override def toString =
      this match
        case Promoted(base) => s"[$base]"
  end TParamLbl

  object Lbl:
    type Basal[V] = Base[V] | Abstracted[V]

    def compareBasal[V](a: Basal[V], b: Basal[V])(using
      V: Ordering[V],
    ): Either[Basal[V], Either[Basal[V], Basal[V]]] =
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

    def compareLax[V](a: Lbl[V], b: Lbl[V])(using
      Ordering[V],
    ): Either[Lbl[V], Either[Lbl[V], Lbl[V]]] =
      compareBasal(a.basal, b.basal) match
        case Left(_) => Left(a)
        case Right(Left(_))  => Right(Left(a))
        case Right(Right(_)) => Right(Right(b))

    def compareStrict[V](a: Lbl[V], b: Lbl[V])(using
      Ordering[V],
    ): Either[Lbl[V], Either[Lbl[V], Lbl[V]]] =
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
    def compareStrict[V](a: TParamLbl[V], b: TParamLbl[V])(using
      Ordering[V],
    ): Either[TParamLbl[V], Either[TParamLbl[V], TParamLbl[V]]] =
      (a, b) match
        case (Promoted(x), Promoted(y)) =>
          Lbl.compareStrict(x, y) match
            case Left(z)         => Left(Promoted(z))
            case Right(Left(x))  => Right(Left(Promoted(x)))
            case Right(Right(y)) => Right(Right(Promoted(y)))
  end TParamLbl
}

class LabelsImpl[V](using V: Ordering[V]) extends Labels[V] {
  import LabelsImpl.*

  override type Label       = Val[Lbl[V]]
  override type TParamLabel = Val[TParamLbl[V]]
  def create(v: V): One -⚬ Label =
    const(Lbl.Base(v, AtomicInteger(0)))
  def make(v: V)(using SourcePos, LambdaContext): $[Label] =
    constant(create(v)) // > alsoPrintLine(x => s"Creating $x")
  val split: Label -⚬ (Label |*| Label) =
    mapVal { (lbl: Lbl[V]) =>
      val res = (lbl.mkClone(), lbl.mkClone())
      // println(s"$lbl split into $res")
      res
    } > liftPair
  val compare: (Label |*| Label) -⚬ (Label |+| (Label |+| Label)) =
    λ { case a |*| b =>
      (a ** b) :>> mapVal { case (a, b) =>
        val res = Lbl.compareLax(a, b)
        // println(s"comparing $a and $b resulted in $res")
        res
      } :>> liftEither :>> |+|.rmap(liftEither)
    }
  val neglect: Label -⚬ Done =
    dsl.neglect
    // printLine(x => s"Neglecting $x")

  val neglectTParam: TParamLabel -⚬ Done =
    dsl.neglect
    // printLine(x => s"Neglecting TParam $x")
  val generify: Label -⚬ TParamLabel =
    // mapVal { TParamLbl.Promoted(_) }
    mapVal { x =>
      val res = TParamLbl.Promoted(x)
      // println(s"$x generified to $res")
      res
    }
  val abstractify: TParamLabel -⚬ Label =
    // mapVal { Lbl.Abstracted(_) }
    mapVal { x =>
      val res = Lbl.Abstracted(x, AtomicInteger(0))
      // println(s"$x abstractified to $res")
      res
    }
  val show: Label -⚬ Val[String] =
    // mapVal(_.toString)
    mapVal(x =>
      val res = x.toString
      // println(s"$x converted to string")
      res
    )
  override val alsoShow: Label -⚬ (Label |*| Val[String]) =
    mapVal((x: Lbl[V]) => (x, x.toString)) > liftPair
  val unwrapOriginal: Label -⚬ Val[V] =
    mapVal(_.originalBase)
  val unwrapOriginalTP: TParamLabel -⚬ Val[V] =
    mapVal { case TParamLbl.Promoted(x) => x.originalBase }
  def alsoDebugPrint(f: String => String): Label -⚬ Label =
    alsoPrintLine(x => f(x.toString))
  def alsoDebugPrintTP(f: String => String): TParamLabel -⚬ TParamLabel =
    alsoPrintLine(x => f(x.toString))
  given junctionLabel: Junction.Positive[Label] =
    scalettoLib.junctionVal
  given junctionTParamLabel: Junction.Positive[TParamLabel] =
    scalettoLib.junctionVal

  override lazy val nested: Nested =
    new Nested {
      override val labels: LabelsImpl[V] =
        new LabelsImpl[V]

      override val promote: labels.TParamLabel -⚬ Label =
        abstractify
    }
}
