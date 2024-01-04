package libretto.typology.inference

import libretto.lambda.util.SourcePos
import libretto.scaletto.StarterKit.{*, given}

import java.util.concurrent.atomic.AtomicInteger
import libretto.scaletto.StarterKit

trait Labels[V] {
  type Label

  def create(v: V): One -⚬ Label
  def split: Label -⚬ (Label |*| Label)
  def testEqual: (Label |*| Label) -⚬ (Label |+| (Label |*| Label))
  def compare: (Label |*| Label) -⚬ (Label |+| (Label |+| Label))
  def neglect: Label -⚬ Done
  def unwrapOriginal: Label -⚬ Val[V]

  given junctionLabel: Junction.Positive[Label]
  given closeableCosemigroupLabel: CloseableCosemigroup[Label]

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

  case class IVar[V, ℓ](
    lbl: Lbl[V, ℓ],
    counter: AtomicInteger, // for generating unique tags of lowered (unnested) inference variables
  )

  object IVar {
    def init[V, ℓ](v: V): IVar[V, ℓ] =
      IVar(Lbl.Base(v), AtomicInteger(0))

    def compare[V, ℓ](a: IVar[V, ℓ], b: IVar[V, ℓ])(using
      Ordering[V],
    ): Int =
      a.lbl compare b.lbl

    def lower[V, ℓ](a: IVar[V, S[ℓ]]): IVar[V, ℓ] =
      IVar(
        Lbl.Lowered(a.lbl, a.counter.incrementAndGet()),
        AtomicInteger(0),
      )
  }

  enum Lbl[V, ℓ]:
    case Base(value: V)
    case Lowered(base: Lbl[V, S[ℓ]], tag: Int)

    def originalBase: V =
      this match
        case Base(value)      => value
        case Lowered(base, _) => base.originalBase

    override def toString =
      this match
        case Lowered(base, tag) => s"$base.$tag"
        case Base(value)        => s"{$value}"

    def compare(that: Lbl[V, ℓ])(using
      V: Ordering[V],
    ): Int =
      (this, that) match
        case (Base(x)      , Base(y)      ) => V.compare(x, y)
        case (Base(_)      , Lowered(_, _)) => -1
        case (Lowered(_, _), Base(_)      ) => 1
        case (Lowered(x, _), Lowered(y, _)) => x compare y
  end Lbl
}

private[inference] class LabelsImpl[V, ℓ](using V: Ordering[V]) extends Labels[V] {
  import LabelsImpl.*

  override type Label = Val[IVar[V, ℓ]]

  override def create(v: V): One -⚬ Label =
    const(IVar.init(v))

  override val split: Label -⚬ (Label |*| Label) =
    dup

  override val compare: (Label |*| Label) -⚬ (Label |+| (Label |+| Label)) =
    λ { case a |*| b =>
      (a ** b) :>> mapVal { case (a, b) =>
        val res = IVar.compare(a, b)
        res match
          case 0 => Left(a)
          case i if i < 0 => Right(Left(a))
          case i if i > 0 => Right(Right(b))
      } :>> liftEither :>> |+|.rmap(liftEither)
    }

  override val testEqual: (Label |*| Label) -⚬ (Label |+| (Label |*| Label)) =
    λ { case a |*| b =>
      (a ** b) :>> mapVal { case (a, b) =>
        val res = IVar.compare(a, b)
        res match {
          case 0 => Left(a)
          case _ => Right((a, b))
        }
      } :>> liftEither :>> |+|.rmap(liftPair)
    }

  override val neglect: Label -⚬ Done =
    dsl.neglect
    // printLine(x => s"Neglecting $x")

  override val show: Label -⚬ Val[String] =
    // mapVal(_.toString)
    mapVal(x =>
      val res = x.toString
      // println(s"$x converted to string")
      res
    )

  override val alsoShow: Label -⚬ (Label |*| Val[String]) =
    mapVal((x: IVar[V, ℓ]) => (x, x.lbl.toString)) > liftPair

  override val unwrapOriginal: Label -⚬ Val[V] =
    mapVal(_.lbl.originalBase)

  override def alsoDebugPrint(f: String => String): Label -⚬ Label =
    alsoPrintLine(x => f(x.toString))

  override given junctionLabel: Junction.Positive[Label] =
    scalettoLib.junctionVal

  override given closeableCosemigroupLabel: CloseableCosemigroup[Label] =
    closeableCosemigroupVal[IVar[V, ℓ]]

  override lazy val nested: Nested =
    new Nested {
      override val labels: LabelsImpl[V, S[ℓ]] =
        new LabelsImpl[V, S[ℓ]]

      override val lower: labels.Label -⚬ Label =
        mapVal(IVar.lower[V, ℓ])
    }
}
