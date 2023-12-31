package libretto.typology.inference

import libretto.lambda.util.SourcePos
import libretto.scaletto.StarterKit._

import java.util.concurrent.atomic.AtomicInteger
import libretto.scaletto.StarterKit

trait Labels[V] {
  type Label

  def create(v: V): One -⚬ Label
  def split: Label -⚬ (Label |*| Label)
  def compare: (Label |*| Label) -⚬ (Label |+| (Label |+| Label))
  def neglect: Label -⚬ Done
  def unwrapOriginal: Label -⚬ Val[V]

  given junctionLabel: Junction.Positive[Label]

  def show: Label -⚬ Val[String]
  def alsoShow: Label -⚬ (Label |*| Val[String])
  def alsoDebugPrint(f: String => String): Label -⚬ Label

  trait Nested {
    val labels: Labels[V]

    def lower: labels.Label -⚬ Label
  }

  def nested: Nested
}

object Labels {
  def apply[V](using Ordering[V]): Labels[V] =
    import LabelsImpl.Z
    new LabelsImpl[V, Z]
}

private[inference] object LabelsImpl {
  sealed trait Z    // level 0
  sealed trait S[N] // level N + 1

  enum Lbl[V, ℓ]:
    case Base(value: V, counter: AtomicInteger)
    case Clone(base: Lbl[V, ℓ], tag: Int)
    case Lowered(base: Lbl[V, S[ℓ]], counter: AtomicInteger)

    import Lbl.Basal

    def basal: Basal[V, ℓ] =
      this match
        case Clone(base, _)     => base.basal
        case x: Base[V, ℓ]    => x
        case x: Lowered[V, ℓ] => x

    def mkClone(): Lbl[V, ℓ] =
      this match
        case b @ Base(_, counter)    => Clone(b, counter.incrementAndGet())
        case b @ Lowered(_, counter) => Clone(b, counter.incrementAndGet())
        case Clone(base, _)          => base.mkClone()

    def declone: (Basal[V, ℓ], List[Int]) =
      def go(lbl: Lbl[V, ℓ], acc: List[Int]): (Basal[V, ℓ], List[Int]) =
        lbl match
          case Clone(base, tag) => go(base, tag :: acc)
          case x: Base[V, ℓ]    => (x, acc)
          case x: Lowered[V, ℓ] => (x, acc)
      go(this, Nil)

    def originalBase: V =
      this match
        case Base(value, _) => value
        case Clone(base, tag) => base.originalBase
        case Lowered(base, _) => base.originalBase

    override def toString =
      this match
        case Lowered(base, _) => s"[$base]+"
        case Base(value, _)   => s"{$value}"
        case Clone(base, tag) => s"$base.$tag"
  end Lbl

  object Lbl:
    type Basal[V, ℓ] = Base[V, ℓ] | Lowered[V, ℓ]

    def compareBasal[V, ℓ](a: Basal[V, ℓ], b: Basal[V, ℓ])(using
      V: Ordering[V],
    ): Either[Basal[V, ℓ], Either[Basal[V, ℓ], Basal[V, ℓ]]] =
      (a, b) match
        case (Base(x, _), Base(y, _)) =>
          V.compare(x, y) match {
            case 0 => Left(a)
            case i if i < 0 => Right(Left (a))
            case i if i > 0 => Right(Right(b))
          }
        case (Base(_, _), Lowered(_, _)) =>
          Right(Left(a))
        case (Lowered(_, _), Base(_, _)) =>
          Right(Right(b))
        case (Lowered(x, _), Lowered(y, _)) =>
          compareStrict(x, y) match
            case Left(z)         => Left(a)
            case Right(Left(_))  => Right(Left(a))
            case Right(Right(_)) => Right(Right(b))

    def compareLax[V, ℓ](a: Lbl[V, ℓ], b: Lbl[V, ℓ])(using
      Ordering[V],
    ): Either[Lbl[V, ℓ], Either[Lbl[V, ℓ], Lbl[V, ℓ]]] =
      compareBasal(a.basal, b.basal) match
        case Left(_) => Left(a)
        case Right(Left(_))  => Right(Left(a))
        case Right(Right(_)) => Right(Right(b))

    def compareStrict[V, ℓ](a: Lbl[V, ℓ], b: Lbl[V, ℓ])(using
      Ordering[V],
    ): Either[Lbl[V, ℓ], Either[Lbl[V, ℓ], Lbl[V, ℓ]]] =
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
}

private[inference] class LabelsImpl[V, ℓ](using V: Ordering[V]) extends Labels[V] {
  import LabelsImpl.*

  override type Label = Val[Lbl[V, ℓ]]

  def create(v: V): One -⚬ Label =
    const(Lbl.Base(v, AtomicInteger(0)))

  def make(v: V)(using SourcePos, LambdaContext): $[Label] =
    constant(create(v)) // > alsoPrintLine(x => s"Creating $x")

  val split: Label -⚬ (Label |*| Label) =
    mapVal { (lbl: Lbl[V, ℓ]) =>
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

  val show: Label -⚬ Val[String] =
    // mapVal(_.toString)
    mapVal(x =>
      val res = x.toString
      // println(s"$x converted to string")
      res
    )

  override val alsoShow: Label -⚬ (Label |*| Val[String]) =
    mapVal((x: Lbl[V, ℓ]) => (x, x.toString)) > liftPair

  val unwrapOriginal: Label -⚬ Val[V] =
    mapVal(_.originalBase)

  def alsoDebugPrint(f: String => String): Label -⚬ Label =
    alsoPrintLine(x => f(x.toString))

  given junctionLabel: Junction.Positive[Label] =
    scalettoLib.junctionVal

  override lazy val nested: Nested =
    new Nested {
      override val labels: LabelsImpl[V, S[ℓ]] =
        new LabelsImpl[V, S[ℓ]]

      override val lower: labels.Label -⚬ Label =
        mapVal { Lbl.Lowered(_, AtomicInteger(0)) }
    }
}
