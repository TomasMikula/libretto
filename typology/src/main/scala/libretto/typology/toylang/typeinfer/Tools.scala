package libretto.typology.toylang.typeinfer

import libretto.lambda.{MonoidalObjectMap, SymmetricMonoidalCategory}
import libretto.lambda.util.{SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.scaletto.StarterKit._
import libretto.typology.kinds.{×, ○, ●}
import libretto.typology.toylang.terms.TypedFun
import libretto.typology.toylang.types.{AbstractTypeLabel, ScalaTypeParam, TypeAlgebra, TypeTag}
import libretto.scaletto.StarterKit
import libretto.lambda.UnhandledCase

trait Tools { self =>
  type Label

  type OutboundType

  type SplittableType

  type MergeableType

  type OutwardType

  type Type = TypedFun.Type

  trait Nested {
    type InterimType

    val tools: Tools

    def lower: tools.OutwardType -⚬ self.OutboundType
    def unnest: tools.OutboundType -⚬ self.OutboundType
    def unnestS: tools.SplittableType -⚬ self.OutboundType
    def unnestM: tools.MergeableType -⚬ self.OutboundType
    def unnestOutward: tools.OutwardType -⚬ self.OutwardType
    def mergeLower: (tools.OutwardType |*| tools.OutwardType) -⚬ self.OutboundType
    def mergeZap: (tools.OutwardType |*| tools.OutwardType) -⚬ Val[Type]
  }

  def label(v: AbstractTypeLabel): One -⚬ Label
  def abstractTypeTap: Label -⚬ (OutboundType |*| Val[Type])
  def abstractLink: Label -⚬ (OutboundType |*| OutboundType)
  def mergeable: OutboundType -⚬ MergeableType
  def splittable: OutboundType -⚬ SplittableType
  def merge: (MergeableType |*| MergeableType) -⚬ MergeableType
  def split: SplittableType -⚬ (SplittableType |*| SplittableType)
  def output: OutboundType -⚬ Val[Type]
  def outputOW: OutwardType -⚬ Val[Type]
  def close: OutboundType -⚬ Done
  def closeOW: OutwardType -⚬ Done
  def tap: OutboundType -⚬ OutwardType
  def tapS: SplittableType -⚬ OutwardType
  def tapM: MergeableType -⚬ OutwardType

  def abstractTypeTapS: Label -⚬ (SplittableType |*| Val[Type]) =
    abstractTypeTap > fst(splittable)

  def abstractTypeTapM: Label -⚬ (MergeableType |*| Val[Type]) =
    abstractTypeTap > fst(mergeable)

  def abstractTypeSplit: Label -⚬ (SplittableType |*| Val[Type] |*| SplittableType) =
    abstractTypeTapS > λ { case s |*| t =>
      val s1 |*| s2 = split(s)
      s1 |*| t |*| s2
    }

  def outputS: SplittableType -⚬ Val[Type] =
    tapS > outputOW

  def outputM: MergeableType -⚬ Val[Type] =
    tapM > outputOW

  def closeS: SplittableType -⚬ Done =
    tapS > closeOW

  def closeM: MergeableType -⚬ Done =
    tapM > closeOW

  /*
   * Language-specific operations.
   *
   * TODO: abstract away
   */

  def debugPrintGradually: OutboundType -⚬ Done
  def pair: (OutboundType |*| OutboundType) -⚬ OutboundType
  def pairOW: (OutwardType |*| OutwardType) -⚬ OutwardType
  def isPair: OutwardType -⚬ (OutwardType |+| (OutwardType |*| OutwardType))
  def recCall: (OutboundType |*| OutboundType) -⚬ OutboundType
  def recCallOW: (OutwardType |*| OutwardType) -⚬ OutwardType
  def isRecCall: OutwardType -⚬ (OutwardType |+| (OutwardType |*| OutwardType))
  def either: (OutboundType |*| OutboundType) -⚬ OutboundType
  def eitherOW: (OutwardType |*| OutwardType) -⚬ OutwardType
  def int: Done -⚬ OutboundType
  def intOW: Done -⚬ OutwardType
  def string: Done -⚬ OutboundType
  def stringOW: Done -⚬ OutwardType
  def fixT[F[_]](F: TypeTag[F]): One -⚬ OutboundType
  def fixTOW[F[_]](F: TypeTag[F]): One -⚬ OutwardType
  def apply1T[F[_]](F: TypeTag[F]): OutboundType -⚬ OutboundType
  def apply1TOW[F[_]](F: TypeTag[F]): OutwardType -⚬ OutwardType

  lazy val nested: Nested
}

object Tools {

  private given Ordering[Either[ScalaTypeParam, AbstractTypeLabel]] with {
    private val ScalaTypeParamOrdering =
      Ordering.Tuple3[String, Int, String]

    override def compare(
      x: Either[ScalaTypeParam, AbstractTypeLabel],
      y: Either[ScalaTypeParam, AbstractTypeLabel],
    ): Int =
      (x, y) match
        case (Left(ScalaTypeParam(f1, l1, n1)), Left(ScalaTypeParam(f2, l2, n2))) =>
          ScalaTypeParamOrdering.compare((f1, l1, n1), (f2, l2, n2))
        case (Left(_), Right(_)) => -1
        case (Right(_), Left(_)) => 1
        case (Right(AbstractTypeLabel(x)), Right(AbstractTypeLabel(y))) => x compareTo y
  }

  val labels = Labels[Either[ScalaTypeParam, AbstractTypeLabel]]

  import labels.{Label, TParamLabel}

  private[typeinfer] object ToolsImpl {
    opaque type TypeEmitter[T] = Rec[[X] =>> TypeEmitterF[T, ReboundTypeF[T, X]]]
    opaque type ReboundType[T] = Rec[[X] =>> ReboundTypeF[T, TypeEmitterF[T, X]]]
    private type TypeEmitterF[T, Y] = Rec[TypeSkelet[T, Y, _]]
    private type ReboundTypeF[T, Y] = Rec[TypeSkelet[-[T], Y, _]]

    private type TypeSkelet[T, Y, X] = NonAbstractTypeF[X] |+| AbstractTypeF[T, Y, X]

    private type ConcreteType[T] = Rec[ConcreteTypeF[T, _]]
    private type ConcreteTypeF[T, X] = NonAbstractTypeF[X] |+| TypeParamF[T]

    private type DegenericType = Rec[DegenericTypeF]
    private type DegenericTypeF[X] = NonAbstractTypeF[X] |+| Label

    type Type = TypedFun.Type // libretto.typology.toylang.types.Type[AbstractTypeLabel]
    def  Type = TypedFun.Type // libretto.typology.toylang.types.Type

    type TypeFun[K, L] = libretto.typology.toylang.types.TypeFun[ScalaTypeParam, K, L]
    // def  TypeFun = libretto.typology.toylang.types.TypeFun

    type TypeTagF = libretto.typology.toylang.types.TypeFun[ScalaTypeParam, ●, ●]

    private[typeinfer] type NonAbstractTypeF[X] = (
      Val[(Type, Type)] // type mismatch
      |+| Done // unit
      |+| Done // int
      |+| Done // string
      |+| Val[TypeTagF] // fix
      |+| (X |*| X) // recCall
      |+| (X |*| X) // either
      |+| (X |*| X) // pair
    )

    private type NonAbstractType[T] = NonAbstractTypeF[TypeEmitter[T]]

    /** Type param instantiable to types of "type" T. */
    private type TypeParamF[T] = TParamLabel |*| -[T]

    private type AbstractTypeF[T, Y, X] = Label |*| RefinementRequestF[T, Y, X]
    private type RefinementRequestF[T, Y, X] = -[ReboundF[T, Y, X]]

    private type AbstractType[T] = AbstractTypeF[T, ReboundType[T], TypeEmitter[T]]
    private type RefinementRequest[T] = RefinementRequestF[T, ReboundType[T], TypeEmitter[T]]

    private type ReboundF[T, Y, X] = (
      Y // refinement
      |+| YieldF[T, X] // refinement won't come from here
    )

    private type YieldF[T, TypeEmitter] = -[
      TypeEmitter // refinement came from elsewhere
      |+| -[T] // there won't be any more internal refinement, open to a type parameter from the outside
    ] |+| One // disengage (providing no refinement, interested in no further refinement)

    private type Rebound[T] = ReboundF[T, ReboundType[T], TypeEmitter[T]]
    private type Yield[T] = YieldF[T, TypeEmitter[T]]

    private type TypeOutletF[T, X] = NonAbstractTypeF[X] |+| T
    private type TypeOutlet[T] = Rec[TypeOutletF[T, _]]

    private object TypeOutlet {
      def pack[T]: (NonAbstractTypeF[TypeOutlet[T]] |+| T) -⚬ TypeOutlet[T] =
        dsl.pack[TypeOutletF[T, _]]

      def unpack[T]: TypeOutlet[T] -⚬ (NonAbstractTypeF[TypeOutlet[T]] |+| T) =
        dsl.unpack

      def nonAbstractType[T]: NonAbstractTypeF[TypeOutlet[T]] -⚬ TypeOutlet[T] =
        injectL > pack

      def typeArg[T]: T -⚬ TypeOutlet[T] =
        injectR > pack
    }

    object RefinementRequest {
      def map[T, Y, X, Q](g: X -⚬ Q): RefinementRequestF[T, Y, X] -⚬ RefinementRequestF[T, Y, Q] =
        contrapositive(Rebound.contramap(g))

      def contramap[T, Y, X, P](f: P -⚬ Y): RefinementRequestF[T, Y, X] -⚬ RefinementRequestF[T, P, X] =
        contrapositive(Rebound.map(f))

      def contramapT[T, Y, X, U](f: T -⚬ U): RefinementRequestF[U, Y, X] -⚬ RefinementRequestF[T, Y, X] =
        contrapositive(Rebound.mapT(f))

      def completeWith[T, Y, X]: (RefinementRequestF[T, Y, X] |*| Y) -⚬ One =
        λ { case req |*| y => injectL(y) supplyTo req }

      def decline[T, Y, X]: RefinementRequestF[T, Y, X] -⚬ (X |+| -[T]) =
        λ { req =>
          req
            .contramap(injectR ∘ injectL)
            .unInvertWith(forevert > swap)
        }

      def grant[T, Y, X]: RefinementRequestF[T, Y, X] -⚬ -[Y] =
        contrapositive(injectL)

      // def decline0[T, Y, X]: RefinementRequestF[T, Y, X] -⚬ One =
      //   λ { req =>
      //     req.contramap(injectR ∘ injectR) :>> unInvertOne
      //   }

      // def merge[T, Y, X](
      //   splitY: Y -⚬ (Y |*| Y),
      // ): (RefinementRequestF[T, Y, X] |*| RefinementRequestF[T, Y, X]) -⚬ RefinementRequestF[T, Y, X] =
      //   λ { case -(r1) |*| -(r2) =>
      //     (Rebound.dup(splitY) >>: (r1 |*| r2)).asInputInv
      //   }

      // def mergeFlip[T, Y, X](
      //   mergeX: (X |*| X) -⚬ X,
      //   splitX: X -⚬ (X |*| X),
      //   flipSplitX: X -⚬ (Y |*| Y),
      //   mergeFlipX: (X |*| X) -⚬ Y,
      //   newAbstractLink: One -⚬ (X |*| Y),
      //   instantiate: X -⚬ T,
      // ): (RefinementRequestF[T, Y, X] |*| RefinementRequestF[T, Y, X]) -⚬ RefinementRequestF[-[T], X, Y] =
      //   λ { case -(r1) |*| -(r2) =>
      //     (Rebound.flopSplit(mergeX, splitX, flipSplitX, mergeFlipX, newAbstractLink, instantiate) >>: (r1 |*| r2)).asInputInv
      //   }

      // def mergeOpWith[P, Q, Y, X](
      //   splitX: X -⚬ (X |*| X),
      //   mergeInXY: (X |*| Y) -⚬ X,
      //   tapFlopYX: Y -⚬ (Y |*| X),
      //   makeP: Y -⚬ P,
      //   makeQ: X -⚬ Q,
      //   tapFlipPQ: P -⚬ (P |*| Q),
      // ): (RefinementRequestF[P, Y, X] |*| RefinementRequestF[Q, X, Y]) -⚬ RefinementRequestF[P, Y, X] =
      //   factorOutInversion > contrapositive(Rebound.tapFlipWith[P, Q, Y, X](splitX, mergeInXY, tapFlopYX, makeP, makeQ, tapFlipPQ))

      // def mergeIn[T, Y, X](
      //   tapFlopY: Y -⚬ (Y |*| X),
      //   mergeInXY: (X |*| Y) -⚬ X,
      //   mergeInXT: (X |*| T) -⚬ X,
      //   yt: Y -⚬ T,
      //   mergeT: (T |*| T) -⚬ T,
      // ): (RefinementRequestF[T, Y, X] |*| RefinementRequestF[-[T], X, Y]) -⚬ RefinementRequestF[T, Y, X] =
      //   factorOutInversion > contrapositive(Rebound.tapFlip[T, Y, X](tapFlopY, mergeInXY, mergeInXT, yt, mergeT))

      // def flopSplit[T, Y, X]: RefinementRequestF[T, Y, X] -⚬ (RefinementRequestF[-[T], X, Y] |*| RefinementRequestF[-[T], X, Y]) =
      //   ???

      // def tapFlop[T, Y, X](
      //   splitX: X -⚬ (X |*| X),
      //   mergeInXY: (X |*| Y) -⚬ X,
      //   tapFlop: Y -⚬ (Y |*| X),
      //   mergeT: (T |*| T) -⚬ T,
      // ): RefinementRequestF[-[T], X, Y] -⚬ (RefinementRequestF[-[T], X, Y] |*| RefinementRequestF[T, Y, X]) =
      //   contrapositive(Rebound.mergeFlip(splitX, mergeInXY, tapFlop, mergeT)) > distributeInversion

      def split[T, Y, X](
        splitX: X -⚬ (X |*| X),
        mergeY: (Y |*| Y) -⚬ Y,
        tapFlop: Y -⚬ (Y |*| X),
        mergeT: (T |*| T) -⚬ T,
      ): RefinementRequestF[T, Y, X] -⚬ (RefinementRequestF[T, Y, X] |*| RefinementRequestF[T, Y, X]) =
        λ { case -(r) =>
          val r1 |*| r2 = Rebound.merge(splitX, mergeY, tapFlop, mergeT) >>: r
          r1.asInputInv |*| r2.asInputInv
        }

      def splitH[T, Y, X](
        splitXY: X -⚬ (X |*| Y),
        mergeYX: (Y |*| X) -⚬ Y,
        splitYPreferred: Y -⚬ (Y |*| Y),
        splitXYPreferred: X -⚬ (X |*| Y),
        splitTPreferred: T -⚬ (T |*| T),
      ): RefinementRequestF[T, Y, X] -⚬ (RefinementRequestF[T, Y, X] |*| RefinementRequestF[-[T], X, Y]) =
        λ { case -(r) =>
          val r1 |*| r2 = Rebound.mergeH(splitXY, mergeYX, splitYPreferred, splitXYPreferred, splitTPreferred) >>: r
          r1.asInputInv |*| r2.asInputInv
        }
    }

    object Rebound {
      def map[T, Y, X, Q](f: Y -⚬ Q): ReboundF[T, Y, X] -⚬ ReboundF[T, Q, X] =
        |+|.lmap(f)

      def contramap[T, Y, X, P](g: P -⚬ X): ReboundF[T, Y, X] -⚬ ReboundF[T, Y, P] =
        |+|.rmap(Yield.contramap(g))

      def mapT[T, Y, X, U](f: T -⚬ U): ReboundF[T, Y, X] -⚬ ReboundF[U, Y, X] =
        |+|.rmap(Yield.mapT(f))

      def unrefined[T, Y, X]: -[X |+| -[T]] -⚬ ReboundF[T, Y, X] =
        injectR ∘ injectL

      def makeUnrefined[T, Y, X]: One -⚬ (ReboundF[T, Y, X] |*| (X |+| -[T])) =
        demand[X |+| -[T]] > fst(unrefined)

      def merge[T, Y, X](
        splitX: X -⚬ (X |*| X),
        mergeY: (Y |*| Y) -⚬ Y,
        tapFlop: Y -⚬ (Y |*| X),
        mergeT: (T |*| T) -⚬ T,
      ): (ReboundF[T, Y, X] |*| ReboundF[T, Y, X]) -⚬ ReboundF[T, Y, X] =
        λ { case a |*| b =>
          a switch {
            case Left(refinedA) =>
              b switch {
                case Left(refinedB) =>
                  injectL(mergeY(refinedA |*| refinedB))
                case Right(yieldB) =>
                  yieldB switch {
                    case Left(yieldB) =>
                      val y |*| x = tapFlop(refinedA)
                      returning(
                        injectL(y),
                        injectL(x) supplyTo yieldB,
                      )
                    case Right(?(_)) =>
                      injectL(refinedA)
                  }
              }
            case Right(yieldA) =>
              b switch {
                case Left(refinedB) =>
                  yieldA switch {
                    case Left(yieldA) =>
                      val y |*| x = tapFlop(refinedB)
                      returning(
                        injectL(y),
                        injectL(x) supplyTo yieldA,
                      )
                    case Right(?(_)) =>
                      injectL(refinedB)
                  }
                case Right(yieldB) =>
                  injectR((yieldA |*| yieldB) :>> Yield.merge(splitX, mergeT))
              }
          }
        }

      def mergeH[T, Y, X](
        splitXY: X -⚬ (X |*| Y),
        mergeYX: (Y |*| X) -⚬ Y,
        splitYPreferred: Y -⚬ (Y |*| Y),
        splitXYPreferred: X -⚬ (X |*| Y),
        splitTPreferred: T -⚬ (T |*| T),
      ): (ReboundF[T, Y, X] |*| ReboundF[-[T], X, Y]) -⚬ ReboundF[T, Y, X] =
        λ { case a |*| b =>
          a switch {
            case Left(refinedA) =>
              b switch {
                case Left(refinedB) =>
                  injectL(mergeYX(refinedA |*| refinedB))
                case Right(yieldB) =>
                  yieldB switch {
                    case Left(yieldB) =>
                      val y1 |*| y2 = splitYPreferred(refinedA)
                      returning(
                        injectL(y2),
                        injectL(y1) supplyTo yieldB,
                      )
                    case Right(?(_)) =>
                      injectL(refinedA)
                  }
              }
            case Right(yieldA) =>
              b switch {
                case Left(refinedB) =>
                  yieldA switch {
                    case Left(yieldA) =>
                      val x |*| y = splitXYPreferred(refinedB)
                      returning(
                        injectL(y),
                        injectL(x) supplyTo yieldA,
                      )
                    case Right(?(_)) =>
                      refinedB :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
                  }
                case Right(yieldB) =>
                  injectR((yieldA |*| yieldB) :>> Yield.mergeH(splitXY, splitTPreferred))
              }
          }
        }

      def unifyRebounds[T, Y, X](
        splitX: X -⚬ (X |*| X),
        mergeY: (Y |*| Y) -⚬ Y,
        tapFlop: Y -⚬ (Y |*| X),
        mergeT: (T |*| T) -⚬ T,
      ): (ReboundF[T, Y, X] |*| ReboundF[T, Y, X]) -⚬ ReboundF[T, Y, X] =
        λ { case l |*| r =>
          l switch {
            case Left(refinedL) =>
              r switch {
                case Left(refinedR) =>
                  injectL(mergeY(refinedL |*| refinedR))
                case Right(unrefinedR) =>
                  unrefinedR switch {
                    case Left(unrefinedR) =>
                      val y |*| x = tapFlop(refinedL)
                      returning(
                        injectL(y),
                        injectL(x) supplyTo unrefinedR,
                      )
                    case Right(?(_)) =>
                      injectL(refinedL)
                  }
              }
            case Right(unrefinedL) =>
              unrefinedL switch {
                case Left(unrefinedL) =>
                  r switch {
                    case Left(refinedR) =>
                      val y |*| x = tapFlop(refinedR)
                      returning(
                        injectL(y),
                        injectL(x) supplyTo unrefinedL,
                      )
                    case Right(unrefinedR) =>
                      unrefinedR switch {
                        case Left(unrefinedR) =>
                          val out |*| res = constant(Rebound.makeUnrefined[T, Y, X])
                          returning(
                            out,
                            res switch {
                              case Left(x) =>
                                val x1 |*| x2 = splitX(x)
                                returning(
                                  injectL(x1) supplyTo unrefinedL,
                                  injectL(x2) supplyTo unrefinedR,
                                )
                              case Right(nt) =>
                                val --(t1) = unrefinedL.contramap(injectR)
                                val --(t2) = unrefinedR.contramap(injectR)
                                mergeT(t1 |*| t2) supplyTo nt
                            }
                          )
                        case Right(?(_)) =>
                          Rebound.unrefined(unrefinedL)
                      }
                  }
                case Right(?(_)) =>
                  r switch {
                    case Left(refinedR) =>
                      injectL(refinedR)
                    case Right(unrefinedR) =>
                      unrefinedR switch {
                        case Left(unrefinedR) =>
                          Rebound.unrefined(unrefinedR)
                        case Right(?(_)) =>
                          constant(crashNow(s"TODO: eliminate this case (at ${summon[SourcePos]})"))
                      }
                  }
              }
          }
        }
    }

    object Yield {
      import TypeEmitter.given

      def contramap[T, X, P](g: P -⚬ X): YieldF[T, X] -⚬ YieldF[T, P] =
        |+|.lmap(contrapositive(|+|.lmap(g)))

      def mapT[T, X, U](g: T -⚬ U): YieldF[T, X] -⚬ YieldF[U, X] =
        |+|.lmap(contrapositive(|+|.rmap(contrapositive(g))))

      def merge[T, X](
        splitX: X -⚬ (X |*| X),
        mergeT: (T |*| T) -⚬ T,
      ): (YieldF[T, X] |*| YieldF[T, X]) -⚬ YieldF[T, X] =
        λ { case a |*| b =>
          a switch {
            case Left(-(a)) =>
              b switch {
                case Left(-(b)) =>
                  producing { r =>
                    (a |*| b) :=
                      (injectL >>: r).asInput switch {
                        case Left(x) =>
                          val x1 |*| x2 = splitX(x)
                          injectL(x1) |*| injectL(x2)
                        case Right(t) =>
                          val t1 |*| t2 = t.contramap(mergeT) :>> distributeInversion
                          injectR(t1) |*| injectR(t2)
                      }
                  }
                case Right(?(_)) =>
                  producing { r =>
                    (r |*| a) := constant(crashNow("unexpected"))
                  }
              }
            case Right(?(_)) =>
              b :>> crashNow("TODO: eliminate this case")
          }
        }

      def mergeH[T, X, Y](
        splitXY: X -⚬ (X |*| Y),
        splitTPreferred: T -⚬ (T |*| T),
        // mergeT: (T |*| T) -⚬ T,
      ): (YieldF[T, X] |*| YieldF[-[T], Y]) -⚬ YieldF[T, X] =
        λ { case a |*| b =>
          a switch {
            case Left(a) =>
              b switch {
                case Left(b) =>
                  producing.demand { (r: $[X |+| -[T]]) =>
                    r switch {
                      case Left(x) =>
                        val x1 |*| y1 = splitXY(x)
                        returning(
                          injectL(x1) supplyTo a,
                          injectL(y1) supplyTo b,
                        )
                      case Right(nt) =>
                        val --(t1)  = a :>> contrapositive(injectR)
                        val --(nt2) = b :>> contrapositive(injectR)
                        val t2 |*| tOut = t1 :>> splitTPreferred
                        returning(
                          t2 supplyTo nt2,
                          tOut supplyTo nt,
                        )
                    }
                  } > injectL
                case Right(?(_)) =>
                  a :>> crashNow("unexpected")
              }
            case Right(?(_)) =>
              b :>> crashNow("TODO: eliminate this case")
          }
        }
    }

    object ReboundTypeF {
      def pack[T, Y]: TypeSkelet[-[T], Y, ReboundTypeF[T, Y]] -⚬ ReboundTypeF[T, Y] =
        dsl.pack

      def unpack[T, Y]: ReboundTypeF[T, Y] -⚬ TypeSkelet[-[T], Y, ReboundTypeF[T, Y]] =
        dsl.unpack

      def contramap[T, Y, P](f: P -⚬ Y): ReboundTypeF[T, Y] -⚬ ReboundTypeF[T, P] =
        rec { self =>
          unpack[T, Y] > TypeSkelet.dimap(f, self) > pack[T, P]
        }
    }

    object ReboundType {
      def pack0[T]: ReboundTypeF[T, TypeEmitterF[T, ReboundType[T]]] -⚬ ReboundType[T] =
        dsl.pack[[X] =>> ReboundTypeF[T, TypeEmitterF[T, X]]]

      def unpack0[T]: ReboundType[T] -⚬ ReboundTypeF[T, TypeEmitterF[T, ReboundType[T]]] =
        dsl.unpack

      def pack1_[T](
        pack1: TypeEmitterF[T, ReboundType[T]] -⚬ TypeEmitter[T],
      ): ReboundTypeF[T, TypeEmitter[T]] -⚬ ReboundType[T] =
        ReboundTypeF.contramap(pack1) > pack0[T]

      private def pack1[T]: ReboundTypeF[T, TypeEmitter[T]] -⚬ ReboundType[T] =
        rec { self =>
          pack1_(TypeEmitter.pack1_(self))
        }

      def unpack1_[T](
        unpack1: TypeEmitter[T] -⚬ TypeEmitterF[T, ReboundType[T]],
      ): ReboundType[T] -⚬ ReboundTypeF[T, TypeEmitter[T]] =
        unpack0[T] > ReboundTypeF.contramap(unpack1)

      private def unpack1[T]: ReboundType[T] -⚬ ReboundTypeF[T, TypeEmitter[T]] =
        rec { self =>
          unpack1_(TypeEmitter.unpack1_(self))
        }

      def unpack[T]: ReboundType[T] -⚬ TypeSkelet[-[T], TypeEmitter[T], ReboundType[T]] =
        λ { t =>
          val t1: $[ReboundTypeF[T, TypeEmitter[T]]] = unpack1(t)
          val t2: $[TypeSkelet[-[T], TypeEmitter[T], ReboundTypeF[T, TypeEmitter[T]]]] = ReboundTypeF.unpack(t1)
          t2 :>> TypeSkelet.map(pack1)
        }

      def pack[T]: TypeSkelet[-[T], TypeEmitter[T], ReboundType[T]] -⚬ ReboundType[T] =
        λ { t =>
          val t1: $[TypeSkelet[-[T], TypeEmitter[T], ReboundTypeF[T, TypeEmitter[T]]]] = t :>> TypeSkelet.map(unpack1)
          val t2: $[ReboundTypeF[T, TypeEmitter[T]]] = ReboundTypeF.pack(t1)
          pack1(t2)
        }

      def map_[S, T](f: S -⚬ T)(
        contramapOutbound: TypeEmitter[T] -⚬ TypeEmitter[S],
      ): ReboundType[S] -⚬ ReboundType[T] = rec { self =>
        unpack > dsl.either(
          NonAbstractType.map(self) > nonAbstractType,
          λ { case l |*| req =>
            val req1 = req
              :>> RefinementRequest.contramapT(contrapositive(f))
              :>> RefinementRequest.contramap(contramapOutbound)
              :>> RefinementRequest.map(self)
            abstractType(l |*| req1)
          },
        )
      }

      def map[S, T](f: S -⚬ T): ReboundType[S] -⚬ ReboundType[T] =
        rec { self =>
          map_(f)(TypeEmitter.contramap_(f)(self))
        }

      def nonAbstractType[T]: NonAbstractTypeF[ReboundType[T]] -⚬ ReboundType[T] =
        injectL > pack

      def abstractType[T]: (Label |*| RefinementRequestF[-[T], TypeEmitter[T], ReboundType[T]]) -⚬ ReboundType[T] =
        injectR > pack

      def makeAbstractType[T]: Label -⚬ (ReboundType[T] |*| ReboundF[-[T], TypeEmitter[T], ReboundType[T]]) =
        TypeSkelet.makeAbstractType[-[T], TypeEmitter[T], ReboundType[T]] > fst(pack)

      def abstractTypeOut[T](
        // outletTParam: (TParamLabel |*| -[T]) -⚬ TypeOutlet[Done],
        outletTParam: (TParamLabel |*| -[T]) -⚬ ConcreteType[Done],
      ): Label -⚬ (ReboundType[T] |*| ConcreteType[Done]) =
        λ { l =>
          val rt |*| resp = makeAbstractType[T](l)
          rt |*| (resp switch {
            case Left(t) =>
              t :>> TypeEmitter.outlet(outletTParam)
            case Right(value) =>
              value switch {
                case Left(req) =>
                  val --(nt) = req :>> contrapositive(injectR)
                  outletTParam(labels.generify(l) |*| nt)
              }
          })
        }

      def abstractTypeTap[T](
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): Label -⚬ (ReboundType[T] |*| Val[Type]) =
        λ { l =>
          val rt |*| resp = makeAbstractType[T](l)
          rt |*| (resp switch {
            case Left(t) =>
              t :>> TypeEmitter.output(outputTParam)
            case Right(value) =>
              value switch {
                case Left(req) =>
                  val --(nt) = req :>> contrapositive(injectR)
                  outputTParam(labels.generify(l) |*| nt)
              }
          })
        }

      def split__[T](
        splitT: T -⚬ (T |*| T),
        mergeOutbound: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
        tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
      ): ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) =
        rec { self =>
          unpack > TypeSkelet.split(
            self,
            mergeOutbound,
            tapFlip,
            factorOutInversion > contrapositive(splitT),
          ) > par(pack, pack)
        }


      def split_[T](
        splitT: T -⚬ (T |*| T),
        mergeOutbound: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
        tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
      ): ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) =
        split__(splitT, mergeOutbound, tapFlip)

      def split[T](
        splitT: T -⚬ (T |*| T),
        outputTParamApprox: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) = rec { self =>
        val tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) =
          TypeEmitter.tapFlip_(splitT, self)

        split_(
          splitT,
          TypeEmitter.merge_(splitT, outputTParamApprox, self),
          tapFlip,
        )
      }

      def splitPreferred__[T](
        splitTPreferred: T -⚬ (T |*| T),
        splitOutboundH: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
        splitOutboundHPreferred1: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
      ): ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) = {
        val mergeNT: (-[T] |*| -[T]) -⚬ -[T] =
          factorOutInversion > contrapositive(splitTPreferred)

        rec { self =>
          unpack > TypeSkelet.splitPreferred(
            self,
            splitOutboundH,
            splitOutboundHPreferred1,
            mergeNT,
            ReboundType.pack,
          )
        }
      }

      def splitPreferred_[T](
        splitTPreferred: T -⚬ (T |*| T),
        splitOutboundH: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
        splitOutboundHPreferred1: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
      ): ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) =
        splitPreferred__(splitTPreferred, splitOutboundH, splitOutboundHPreferred1)

      def splitPreferred[T](
        splitTPreferred: T -⚬ (T |*| T),
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) =
        splitPreferred_(
          splitTPreferred,
          TypeEmitter.splitH(splitTPreferred, outputT, outputTParam),
          TypeEmitter.splitHPreferred1(splitTPreferred, outputT, outputTParam),
        )

      def merge__[T](
        splitOutbound: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
        mergeT: (T |*| T) -⚬ T,
        outputTParam: (TParamLabel |*| T) -⚬ Val[Type],
      )(using
        Junction.Positive[T],
      ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] = {
        import TypeEmitter.junctionTypeEmitter

        rec { self =>
          λ { case a |*| b =>
            (unpack(a) |*| unpack(b))
              :>> TypeSkelet.mergeOp(
                splitOutbound,
                TypeEmitter.pack,
                ReboundType.pack,
                tapFlop_(self, mergeT),
                self,
                outputApprox(outputTParam),
                mergeT,
                outputTParam,
              )
          }
        }
      }

      def merge_[T](
        mergeT: (T |*| T) -⚬ T,
        outputTParam: (TParamLabel |*| T) -⚬ Val[Type],
      )(using
        Junction.Positive[T],
      ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] =
        rec { self =>
          merge__(
            TypeEmitter.split_(
              self,
              tapFlop_(self, mergeT),
              mergeT,
            ),
            mergeT,
            outputTParam,
          )
        }

      def merge[T](
        mergeT: (T |*| T) -⚬ T,
        outputTParam: (TParamLabel |*| T) -⚬ Val[Type],
      )(using
        Junction.Positive[T],
      ): (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T] =
        merge_(
          mergeT,
          outputTParam,
        )

      def mergeH__[T](
        mergeH: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T],
        splitPreferred: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
        splitOutboundH: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
        splitOutboundHPreferred1: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
        splitTPreferred: T -⚬ (T |*| T),
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] = rec { self =>
        par(
          ReboundType.unpack,
          TypeEmitter.unpack > TypeSkelet.contramapT(die),
        ) > TypeSkelet.mergeH[-[T], TypeEmitter[T], ReboundType[T]](
          mergeH,
          splitOutboundH,
          splitPreferred,
          splitOutboundHPreferred1,
          ReboundType.pack[T],
          TypeSkelet.contramapT(dii) > TypeEmitter.pack,
          ReboundType.outputApprox(outputT),
          TypeEmitter.outputApprox[T](outputTParam),
          factorOutInversion > contrapositive(splitTPreferred),
        )
      }

      def mergeH_[T](
        splitOutboundH: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
        splitOutboundHPreferred1: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
        splitTPreferred: T -⚬ (T |*| T),
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] =
        rec { self =>
          mergeH__(
            self,
            splitPreferred__(splitTPreferred, splitOutboundH, splitOutboundHPreferred1),
            splitOutboundH,
            splitOutboundHPreferred1,
            splitTPreferred,
            outputT,
            outputTParam,
          )
        }

      def mergeH[T](
        splitTPreferred: T -⚬ (T |*| T),
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] = rec { self =>
        val (splitOutboundH, splitOutboundHPreferred1) = rec2 { (
          splitOutboundH: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
          splitOutboundHPreferred1: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
        ) =>
          val splitPreferred = splitPreferred_(splitTPreferred, splitOutboundH, splitOutboundHPreferred1)
          (
            TypeEmitter.splitH_(splitTPreferred, self, splitPreferred),
            TypeEmitter.splitHPreferred1_(splitTPreferred, self, splitPreferred),
          )
        }
        mergeH_(
          splitOutboundH,
          splitOutboundHPreferred1,
          splitTPreferred,
          outputT,
          outputTParam,
        )
      }

      def tapFlop_[T](
        merge: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
        mergeT: (T |*| T) -⚬ T,
      ): ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]) = {
        import TypeEmitter.junctionTypeEmitter
        rec { self =>
          val splitX: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
            TypeEmitter.split_(merge, self, mergeT)

          rec { self =>
            unpack > TypeSkelet.tapFlop(splitX, self, TypeEmitter.pack, ReboundType.pack, mergeT)
          }
        }
      }

      def tapFlop[T](
        mergeT: (T |*| T) -⚬ T,
        outputTParam: (TParamLabel |*| T) -⚬ Val[Type],
      )(using
        Junction.Positive[T],
      ): ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]) =
        tapFlop_(
          merge_(mergeT, outputTParam),
          mergeT,
        )

      def output[T](
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
      ): ReboundType[T] -⚬ Val[Type] = {
        val outputT1: (TParamLabel |*| -[-[T]]) -⚬ Val[Type] =
          λ { case lbl |*| --(t) => outputT(lbl |*| t) }

        rec { self =>
          unpack > TypeSkelet.output(self, outputT1)
        }
      }

      def close[T](
        closeT: T -⚬ Done,
      ): ReboundType[T] -⚬ Done = {
        val closeTParam: (TParamLabel |*| -[-[T]]) -⚬ Done =
          λ { case lbl |*| --(t) =>
            join(closeT(t) |*| labels.neglectTParam(lbl))
          }

        rec { self =>
          unpack > TypeSkelet.close(self, closeTParam)
        }
      }

      def probe[T](
        // outletTParam: (TParamLabel |*| -[T]) -⚬ TypeOutlet[Done],
        outletTParam: (TParamLabel |*| -[T]) -⚬ ConcreteType[Done],
      ): (TParamLabel |*| -[ReboundType[T]]) -⚬ ConcreteType[Done] =
        λ { case label |*| nt =>
          val lbl1 |*| lbl2 = labels.split(labels.abstractify(label))
          val t |*| reb = makeAbstractType[T](lbl1)
          returning(
            reb switch {
              case Left(x) =>
                import TypeEmitter.junctionTypeEmitter
                (x waitFor labels.neglect(lbl2))
                  :>> TypeEmitter.outlet(outletTParam)
              case Right(value) =>
                value switch {
                  case Left(req) =>
                    val --(nt) = req contramap injectR
                    val l = labels.generify(lbl2)
                    outletTParam(l |*| nt)
                  case Right(?(_)) =>
                    lbl2 :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
                }
            },
            t supplyTo nt,
          )
        }

      def probeApprox[T](
        outputTypeParamApprox: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): (TParamLabel |*| -[ReboundType[T]]) -⚬ Val[Type] =
        λ { case label |*| nt =>
          val lbl1 |*| lbl2 = labels.split(labels.abstractify(label))
          val t |*| reb = makeAbstractType[T](lbl1)
          returning(
            reb switch {
              case Left(x) =>
                TypeEmitter.outputApprox(outputTypeParamApprox)(x)
                  .waitFor(labels.neglect(lbl2))
              case Right(value) =>
                value switch {
                  case Left(req) =>
                    val --(nt) = req contramap injectR
                    val l = labels.generify(lbl2)
                    outputTypeParamApprox(l |*| nt)
                  case Right(?(_)) =>
                    lbl2 :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
                }
            },
            t supplyTo nt,
          )
        }

      def outputApprox[T](
        outputTParam: (TParamLabel |*| T) -⚬ Val[Type],
      ): ReboundType[T] -⚬ Val[Type] =
        rec { self =>
          unpack > TypeSkelet.outputApprox(
            self,
            snd(die) > outputTParam,
          )
        }

      def outlet[T](
        // outletT: (TParamLabel |*| T) -⚬ TypeOutlet[Done],
        outletT: (TParamLabel |*| T) -⚬ ConcreteType[Done],
      ): ReboundType[T] -⚬ ConcreteType[Done] = rec { self =>
        λ { t =>
          unpack(t) switch {
            case Left(t) =>
              ConcreteType.nonAbstractType(NonAbstractType.map(self)(t))
            case Right(lbl |*| req) =>
              RefinementRequest.decline(req) switch {
                case Left(t)      => self(t)
                case Right(--(t)) => outletT(labels.generify(lbl) |*| t)
              }
          }
        }
      }

      def awaitPosFst[T]: (Done |*| ReboundType[T]) -⚬ ReboundType[T] =
        rec { self =>
          snd(unpack) > TypeSkelet.awaitPosFst(self) > pack
        }

      given junctionReboundType[T]: Junction.Positive[ReboundType[T]] with {
        override def awaitPosFst: (Done |*| ReboundType[T]) -⚬ ReboundType[T] =
          ReboundType.awaitPosFst[T]
      }
    }

    object NonAbstractType {
      def pair[X]: (X |*| X) -⚬ NonAbstractTypeF[X] =
        injectR

      def either[X]: (X |*| X) -⚬ NonAbstractTypeF[X] =
        injectL ∘ injectR

      def recCall[X]: (X |*| X) -⚬ NonAbstractTypeF[X] =
        injectL ∘ injectL ∘ injectR

      def fix[X]: Val[TypeTagF] -⚬ NonAbstractTypeF[X] =
        injectL ∘ injectL ∘ injectL ∘ injectR

      def fixT[X, F[_]](F: TypeTag[F]): One -⚬ NonAbstractTypeF[X] =
        fix ∘ const(TypeTag.toTypeFun(F))

      def apply1T[X, F[_]](
        F: TypeTag[F],
        lift: NonAbstractTypeF[X] -⚬ X,
      )(using Junction.Positive[X]): X -⚬ X =
        apply1(TypeTag.toTypeFun(F), lift)

      def apply1[X](
        f: TypeTagF,
        lift: NonAbstractTypeF[X] -⚬ X,
      )(using J: Junction.Positive[X]): X -⚬ X = {
        val ct = compilationTarget[X](lift)
        import ct.Map_●
        val g: ct.Arr[X, X] = f.compile[ct.Arr, ct.as, X](Map_●)(ct.typeAlgebra, Map_●).get(Map_●, Map_●)
        g > J.awaitPosFst
      }

      def string[X]: Done -⚬ NonAbstractTypeF[X] =
        injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

      def int[X]: Done -⚬ NonAbstractTypeF[X] =
        injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

      def unit[X]: Done -⚬ NonAbstractTypeF[X] =
        injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

      def mismatch[X]: Val[(Type, Type)] -⚬ NonAbstractTypeF[X] =
        injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL

      def isPair[X]: NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[X] |+| (X |*| X)) =
        λ { t =>
          t switch {
            case Right(r |*| s) => // pair
              injectR(r |*| s)
            case Left(t) =>
              injectL(injectL(t))
          }
        }

      def isRecCall[X]: NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[X] |+| (X |*| X)) =
        λ { t =>
          t switch {
            case Right(r |*| s) => // pair
              injectL(pair(r |*| s))
            case Left(t) =>
              t switch {
                case Right(r |*| s) => // either
                  injectL(either(r |*| s))
                case Left(t) =>
                  t switch {
                    case Right(r |*| s) => // RecCall
                      injectR(r |*| s)
                    case Left(t) =>
                      injectL(
                        injectL(injectL(injectL(t)))
                      )
                  }
              }
          }
        }

      def map[X, Q](g: X -⚬ Q): NonAbstractTypeF[X] -⚬ NonAbstractTypeF[Q] =
        λ { t =>
          t switch {
            case Right(r |*| s) => // pair
              pair(g(r) |*| g(s))
            case Left(t) =>
              t switch {
                case Right(r |*| s) => // either
                  either(g(r) |*| g(s))
                case Left(t) =>
                  t switch {
                    case Right(r |*| s) => // RecCall
                      recCall(g(r) |*| g(s))
                    case Left(t) =>
                      t switch {
                        case Right(f) => // fix
                          fix(f)
                        case Left(t) =>
                          t switch {
                            case Right(d) => // string
                              string(d)
                            case Left(t) =>
                              t switch {
                                case Right(d) => // int
                                  int(d)
                                case Left(t) =>
                                  t switch {
                                    case Right(d) => // unit
                                      unit(d)
                                    case Left(err) =>
                                      mismatch(err)
                                  }
                              }
                          }
                      }
                  }
              }
          }
        }

      def splitMap[X, Y, Z](
        f: X -⚬ (Y |*| Z),
      ): NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[Y] |*| NonAbstractTypeF[Z]) =
        λ { t =>
          t switch {
            case Right(r |*| s) => // pair
              val r1 |*| r2 = f(r)
              val s1 |*| s2 = f(s)
              pair(r1 |*| s1) |*| pair(r2 |*| s2)
            case Left(t) =>
              t switch {
                case Right(r |*| s) => // either
                  val r1 |*| r2 = f(r)
                  val s1 |*| s2 = f(s)
                  either(r1 |*| s1) |*| either(r2 |*| s2)
                case Left(t) =>
                  t switch {
                    case Right(r |*| s) => // RecCall
                      val r1 |*| r2 = f(r)
                      val s1 |*| s2 = f(s)
                      recCall(r1 |*| s1) |*| recCall(r2 |*| s2)
                    case Left(t) =>
                      t switch {
                        case Right(+(f)) => // fix
                          fix(f) |*| fix(f)
                        case Left(t) =>
                          t switch {
                            case Right(+(t)) => // string
                              string(t) |*| string(t)
                            case Left(t) =>
                              t switch {
                                case Right(+(t)) => // int
                                  int(t) |*| int(t)
                                case Left(t) =>
                                  t switch {
                                    case Right(+(t)) => // unit
                                      unit(t) |*| unit(t)
                                    case Left(err) =>
                                      err :>> dsl.dup :>> par(mismatch, mismatch)
                                  }
                              }
                          }
                      }
                  }
              }
          }
        }

      def split[X](
        splitX: X -⚬ (X |*| X),
      ): NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[X] |*| NonAbstractTypeF[X]) =
        splitMap(splitX)

      def mergeWith[X, Y, Z](
        g: (X |*| Y) -⚬ Z,
        outputXApprox: X -⚬ Val[Type],
        outputYApprox: Y -⚬ Val[Type],
      ): (NonAbstractTypeF[X] |*| NonAbstractTypeF[Y]) -⚬ NonAbstractTypeF[Z] = {
        λ { case a |*| b =>
          a switch {
            case Right(a1 |*| a2) => // `a` is a pair
              b switch {
                case Right(b1 |*| b2) => // `b` is a pair
                  NonAbstractType.pair(g(a1 |*| b1) |*| g(a2 |*| b2))
                case Left(b) =>
                  NonAbstractType.mismatch(
                    ((outputXApprox(a1) ** outputXApprox(a2)) :>> mapVal { case (a1, a2) => Type.pair(a1, a2) })
                    ** output(outputYApprox)(injectL(b))
                  )
              }
            case Left(a) =>
              b switch {
                case Right(b1 |*| b2) => // `b` is a pair
                  NonAbstractType.mismatch(
                    output(outputXApprox)(injectL(a))
                    ** ((outputYApprox(b1) ** outputYApprox(b2)) :>> mapVal { case (b1, b2) => Type.pair(b1, b2) })
                  )
                case Left(b) =>
                  a switch {
                    case Right(p |*| q) => // `a` is either
                      b switch {
                        case Right(r |*| s) => // `b` is either
                          NonAbstractType.either(g(p |*| r) |*| g(q |*| s))
                        case Left(b) =>
                          NonAbstractType.mismatch(
                            ((outputXApprox(p) ** outputXApprox(q)) :>> mapVal { case (p, q) => Type.sum(p, q) })
                            ** output(outputYApprox)(injectL(injectL(b)))
                          )
                      }
                    case Left(a) =>
                      b switch {
                        case Right(r |*| s) => // `b` is either
                          NonAbstractType.mismatch(
                            output(outputXApprox)(injectL(injectL(a)))
                            ** ((outputYApprox(r) ** outputYApprox(s)) :>> mapVal { case (r, s) => Type.sum(r, s) })
                          )
                        case Left(b) =>
                          a switch {
                            case Right(p |*| q) => // `a` is RecCall
                              b switch {
                                case Right(r |*| s) => // `b` is RecCall
                                  NonAbstractType.recCall(g(p |*| r) |*| g(q |*| s))
                                case Left(b) =>
                                  NonAbstractType.mismatch(
                                    ((outputXApprox(p) ** outputXApprox(q)) :>> mapVal { case (p, q) => Type.recCall(p, q) })
                                    ** output(outputYApprox)(injectL(injectL(injectL(b))))
                                  )
                              }
                            case Left(a) =>
                              b switch {
                                case Right(r |*| s) => // `b` is RecCall
                                  NonAbstractType.mismatch(
                                    output(outputXApprox)(injectL(injectL(injectL(a))))
                                    ** ((outputYApprox(r) ** outputYApprox(s)) :>> mapVal { case (r, s) => Type.recCall(r, s) })
                                  )
                                case Left(b) =>
                                  a switch {
                                    case Right(f) => // `a` is fix
                                      b switch {
                                        case Right(g) => // `b` is fix
                                          ((f ** g) :>> mapVal { case (f, g) =>
                                            if (f == g) Left(f)
                                            else        Right((f, g))
                                          } :>> liftEither) switch {
                                            case Left(f)   => NonAbstractType.fix(f)
                                            case Right(fg) => NonAbstractType.mismatch(fg :>> mapVal { case (f, g) => (Type.fix(f.vmap(Left(_))), Type.fix(g.vmap(Left(_)))) })
                                          }
                                        case Left(b) =>
                                          NonAbstractType.mismatch(
                                            (f :>> mapVal { f => Type.fix(f.vmap(Left(_))) })
                                            ** output(outputYApprox)(injectL(injectL(injectL(injectL(b)))))
                                          )
                                      }
                                    case Left(a) =>
                                      b switch {
                                        case Right(g) => // `b` is fix
                                          NonAbstractType.mismatch(
                                            output(outputXApprox)(injectL(injectL(injectL(injectL(a)))))
                                            ** (g :>> mapVal { g => Type.fix(g.vmap(Left(_))) })
                                          )
                                        case Left(b) =>
                                          a switch {
                                            case Right(x) => // `a` is string
                                              b switch {
                                                case Right(y) => // `b` is string
                                                  NonAbstractType.string(join(x |*| y))
                                                case Left(b) =>
                                                  NonAbstractType.mismatch(
                                                    (x :>> constVal(Type.string))
                                                    ** output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(b))))))
                                                  )
                                              }
                                            case Left(a) =>
                                              b switch {
                                                case Right(y) => // `b` is string
                                                  NonAbstractType.mismatch(
                                                    output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(a))))))
                                                    ** (y :>> constVal(Type.string))
                                                  )
                                                case Left(b) =>
                                                  a switch {
                                                    case Right(x) => // `a` is int
                                                      b switch {
                                                        case Right(y) => // `b` is int
                                                          NonAbstractType.int(join(x |*| y))
                                                        case Left(b) =>
                                                          NonAbstractType.mismatch(
                                                            (x :>> constVal(Type.int))
                                                            ** output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(injectL(b)))))))
                                                          )
                                                      }
                                                    case Left(a) =>
                                                      b switch {
                                                        case Right(y) => // `b` is int
                                                          NonAbstractType.mismatch(
                                                            output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(injectL(a)))))))
                                                            ** (y :>> constVal(Type.int))
                                                          )
                                                        case Left(b) =>
                                                          a switch {
                                                            case Right(x) => // `a` is unit
                                                              b switch {
                                                                case Right(y) => // `b` is unit
                                                                  NonAbstractType.unit(join(x |*| y))
                                                                case Left(bx) => // `b` is type mismatch
                                                                  val tb = bx :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                  val ta = x :>> constVal(Type.unit[TypedFun.Label])
                                                                  NonAbstractType.mismatch(ta ** tb)
                                                              }
                                                            case Left(ax) => // `a` is type mismatch
                                                              val ta = ax :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                              b switch {
                                                                case Right(y) => // `b` is unit
                                                                  val tb = y :>> constVal(Type.unit[TypedFun.Label])
                                                                  NonAbstractType.mismatch(ta ** tb)
                                                                case Left(bx) => // `b` is type mismatch
                                                                  val tb = bx :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                                                  NonAbstractType.mismatch(ta ** tb)
                                                              }
                                                          }
                                                      }
                                                  }
                                              }
                                          }
                                      }
                                  }
                              }
                          }
                      }
                  }
              }
          }
        }
      }

      def merge[X](
        mergeX: (X |*| X) -⚬ X,
        outputXApprox: X -⚬ Val[Type],
      ): (NonAbstractTypeF[X] |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[X] =
        mergeWith[X, X, X](mergeX, outputXApprox, outputXApprox)

      def output[X](
        outputX: X -⚬ Val[Type],
      ): NonAbstractTypeF[X] -⚬ Val[Type] =
        λ { x =>
          x switch {
            case Right(x1 |*| x2) => // pair
              (outputX(x1) ** outputX(x2)) :>> mapVal { case (t1, t2) =>
                Type.pair(t1, t2)
              }
            case Left(x) =>
              x switch {
                case Right(a |*| b) => // either
                  (outputX(a) ** outputX(b)) :>> mapVal { case (a, b) =>
                    Type.pair(a, b)
                  }
                case Left(x) =>
                  x switch {
                    case Right(a |*| b) => // recCall
                      (outputX(a) ** outputX(b)) :>> mapVal { case (a, b) =>
                        Type.recCall(a, b)
                      }
                    case Left(x) =>
                      x switch {
                        case Right(tf) => // fix
                          tf :>> mapVal { tf => Type.fix(tf.vmap(Left(_))) }
                        case Left(x) =>
                          x switch {
                            case Right(x) => // string
                              x :>> constVal(Type.string)
                            case Left(x) =>
                              x switch {
                                case Right(x) => // int
                                  x :>> constVal(Type.int)
                                case Left(x) =>
                                  x switch {
                                    case Right(x) => // unit
                                      x :>> constVal(Type.unit)
                                    case Left(mismatch) =>
                                      mismatch :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
                                  }
                              }
                          }
                      }
                  }
              }
          }
        }

      def close[X](
        closeX: X -⚬ Done,
      ): NonAbstractTypeF[X] -⚬ Done =
        λ { t =>
          t switch {
            case Right(a |*| b) => join(closeX(a) |*| closeX(b))
            case Left(t) => t switch {
              case Right(a |*| b) => join(closeX(a) |*| closeX(b))
              case Left(t) => t switch {
                case Right(a |*| b) => join(closeX(a) |*| closeX(b))
                case Left(t) => t switch {
                  case Right(f) => neglect(f)
                  case Left(t) => t switch {
                    case Right(x) => x
                    case Left(t) => t switch {
                      case Right(x) => x
                      case Left(t) => t switch {
                        case Right(x) => x
                        case Left(e) => neglect(e)
                      }
                    }
                  }
                }
              }
            }
          }
        }

      def awaitPosFst[X](
        g: (Done |*| X) -⚬ X,
      ): (Done |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[X] =
        λ { case d |*| t =>
          t switch {
            case Right(a |*| b) => pair(g(d |*| a) |*| b)
            case Left(t) => t switch {
              case Right(a |*| b) => either(g(d |*| a) |*| b)
              case Left(t) => t switch {
                case Right(a |*| b) => recCall(g(d |*| a) |*| b)
                case Left(t) => t switch {
                  case Right(f) => fix(f waitFor d)
                  case Left(t) => t switch {
                    case Right(x) => string(join(d |*| x))
                    case Left(t) => t switch {
                      case Right(x) => int(join(d |*| x))
                      case Left(t) => t switch {
                        case Right(x) => unit(join(d |*| x))
                        case Left(e) => mismatch(e waitFor d)
                      }
                    }
                  }
                }
              }
            }
          }
        }

      given junctionNonAbstractType[X](using
        X: Junction.Positive[X],
      ): Junction.Positive[NonAbstractTypeF[X]] with {
        override def awaitPosFst: (Done |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[X] =
          NonAbstractType.awaitPosFst[X](X.awaitPosFst)
      }

      class compilationTarget[T](
        lift: NonAbstractTypeF[T] -⚬ T,
      ) {
        type Arr[K, L] = K -⚬ (Done |*| L)

        val category: SymmetricMonoidalCategory[Arr, |*|, One] =
          new SymmetricMonoidalCategory[Arr, |*|, One] {

            override def id[A]: Arr[A, A] =
              dsl.introFst(done)

            override def introFst[A]: Arr[A, One |*| A] =
              dsl.andThen(dsl.introFst, dsl.introFst(done))

            override def introSnd[A]: Arr[A, A |*| One] =
              dsl.andThen(dsl.introSnd, dsl.introFst(done))

            override def elimFst[A]: Arr[One |*| A, A] =
              dsl.fst(done)

            override def elimSnd[A]: Arr[A |*| One, A] =
              dsl.andThen(dsl.swap, dsl.fst(done))

            override def assocRL[A, B, C]: Arr[A |*| (B |*| C), (A |*| B) |*| C] =
              dsl.andThen(dsl.assocRL, dsl.introFst(done))

            override def assocLR[A, B, C]: Arr[(A |*| B) |*| C, A |*| (B |*| C)] =
              dsl.andThen(dsl.assocLR, dsl.introFst(done))

            override def swap[A, B]: Arr[A |*| B, B |*| A] =
              dsl.andThen(dsl.swap, dsl.introFst(done))

            override def andThen[A, B, C](
              f: Arr[A, B],
              g: Arr[B, C],
            ): Arr[A, C] =
              dsl.andThen(
                dsl.andThen(f, dsl.snd(g)),
                dsl.andThen(dsl.assocRL, dsl.fst(join)),
              )

            override def par[A1, A2, B1, B2](
              f1: Arr[A1, B1],
              f2: Arr[A2, B2],
            ): Arr[A1 |*| A2, B1 |*| B2] =
              dsl.andThen(
                dsl.par(f1, f2),
                λ { case (d1 |*| b1) |*| (d2 |*| b2) =>
                  join(d1 |*| d2) |*| (b1 |*| b2)
                },
              )
          }

        val typeAlgebra: TypeAlgebra.Of[ScalaTypeParam, Arr, T, |*|, One] =
          new TypeAlgebra[ScalaTypeParam, Arr] {
            override type Type = T
            override type <*>[A, B] = A |*| B
            override type None = One

            override def unit: Arr[One, T] =
              done > λ { case +(d) => d |*| lift(NonAbstractType.unit(d)) }
            override def int: Arr[One, T] =
              done > λ { case +(d) => d |*| lift(NonAbstractType.int(d)) }
            override def string: Arr[One, T] =
              done > λ { case +(d) => d |*| lift(NonAbstractType.string(d)) }
            override def pair: Arr[T |*| T, T] =
              λ { case t |*| u => constant(done) |*| lift(NonAbstractType.pair(t |*| u)) }
            override def sum: Arr[T |*| T, T] =
              λ { case t |*| u => constant(done) |*| lift(NonAbstractType.either(t |*| u)) }
            override def recCall: Arr[T |*| T, T] =
              λ { case t |*| u => constant(done) |*| lift(NonAbstractType.recCall(t |*| u)) }
            override def fix(f: TypeFun[●, ●]): Arr[One, T] =
              // const(f) > ConcreteType.fix > introFst(done)
              throw NotImplementedError(s"TODO (${summon[SourcePos]})")
            override def abstractTypeName(name: ScalaTypeParam): Arr[One, T] =
              throw NotImplementedError(s"TODO (${summon[SourcePos]})")

            override given category: SymmetricMonoidalCategory[Arr, |*|, One] =
              compilationTarget.this.category
          }

        sealed trait as[K, Q]

        case object Map_○ extends as[○, One]
        case object Map_● extends as[●, T]
        case class Pair[K1, K2, Q1, Q2](
          f1: K1 as Q1,
          f2: K2 as Q2,
        ) extends as[K1 × K2, Q1 |*| Q2]

        given objectMap: MonoidalObjectMap[as, ×, ○, |*|, One] =
          new MonoidalObjectMap[as, ×, ○, |*|, One] {

            override def uniqueOutputType[A, B, C](f: as[A, B], g: as[A, C]): B =:= C =
              (f, g) match {
                case (Map_○, Map_○) => summon[B =:= C]
                case (Map_●, Map_●) => summon[B =:= C]
                case (Pair(f1, f2), Pair(g1, g2)) =>
                  (uniqueOutputType(f1, g1), uniqueOutputType(f2, g2)) match {
                    case (TypeEq(Refl()), TypeEq(Refl())) =>
                      summon[B =:= C]
                  }
              }

            override def pair[A1, A2, X1, X2](f1: as[A1, X1], f2: as[A2, X2]): as[A1 × A2, X1 |*| X2] =
              Pair(f1, f2)

            override def unpair[A1, A2, X](f: as[A1 × A2, X]): Unpaired[A1, A2, X] =
              f match {
                case Pair(f1, f2) => Unpaired.Impl(f1, f2)
              }

            override def unit: as[○, One] =
              Map_○
          }
      }
    }

    object ConcreteType {
      def pack[T]: (NonAbstractTypeF[ConcreteType[T]] |+| TypeParamF[T]) -⚬ ConcreteType[T] =
        dsl.pack[ConcreteTypeF[T, _]]

      def unpack[T]: ConcreteType[T] -⚬ (NonAbstractTypeF[ConcreteType[T]] |+| TypeParamF[T]) =
        dsl.unpack

      def nonAbstractType[T]: NonAbstractTypeF[ConcreteType[T]] -⚬ ConcreteType[T] =
        pack ∘ injectL

      def typeParam[T]: TypeParamF[T] -⚬ ConcreteType[T] =
        pack ∘ injectR

      def pair[T]: (ConcreteType[T] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
        NonAbstractType.pair > nonAbstractType

      def either[T]: (ConcreteType[T] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
        NonAbstractType.either > nonAbstractType

      def recCall[T]: (ConcreteType[T] |*| ConcreteType[T]) -⚬ ConcreteType[T] =
        NonAbstractType.recCall > nonAbstractType

      def fix[T]: Val[TypeTagF] -⚬ ConcreteType[T] =
        NonAbstractType.fix > nonAbstractType

      def fixT[T, F[_]](F: TypeTag[F]): One -⚬ ConcreteType[T] =
        NonAbstractType.fixT(F) > nonAbstractType

      def string[T]: Done -⚬ ConcreteType[T] =
        NonAbstractType.string > nonAbstractType

      def int[T]: Done -⚬ ConcreteType[T] =
        NonAbstractType.int > nonAbstractType

      def unit[T]: Done -⚬ ConcreteType[T]=
        NonAbstractType.unit > nonAbstractType

      def mismatch[T]: Val[(Type, Type)] -⚬ ConcreteType[T] =
        NonAbstractType.mismatch > nonAbstractType

      def apply1T[T, F[_]](F: TypeTag[F]): ConcreteType[T] -⚬ ConcreteType[T] =
        apply1(TypeTag.toTypeFun(F))

      def apply1[T](f: TypeTagF): ConcreteType[T] -⚬ ConcreteType[T] = {
        // λ { t => NonAbstractType.apply1(constantVal(f) |*| t) :>> nonAbstractType }
        val ct = compilationTarget[T]
        import ct.Map_●
        f.compile[ct.Arr, ct.as, ConcreteType[T]](Map_●)(ct.typeAlgebra, Map_●).get(Map_●, Map_●) > awaitPosFst
      }

      class compilationTarget[T] {
        type Arr[K, L] = K -⚬ (Done |*| L)

        val category: SymmetricMonoidalCategory[Arr, |*|, One] =
          new SymmetricMonoidalCategory[Arr, |*|, One] {

            override def id[A]: Arr[A, A] =
              dsl.introFst(done)

            override def introFst[A]: Arr[A, One |*| A] =
              dsl.andThen(dsl.introFst, dsl.introFst(done))

            override def introSnd[A]: Arr[A, A |*| One] =
              dsl.andThen(dsl.introSnd, dsl.introFst(done))

            override def elimFst[A]: Arr[One |*| A, A] =
              dsl.fst(done)

            override def elimSnd[A]: Arr[A |*| One, A] =
              dsl.andThen(dsl.swap, dsl.fst(done))

            override def assocRL[A, B, C]: Arr[A |*| (B |*| C), (A |*| B) |*| C] =
              dsl.andThen(dsl.assocRL, dsl.introFst(done))

            override def assocLR[A, B, C]: Arr[(A |*| B) |*| C, A |*| (B |*| C)] =
              dsl.andThen(dsl.assocLR, dsl.introFst(done))

            override def swap[A, B]: Arr[A |*| B, B |*| A] =
              dsl.andThen(dsl.swap, dsl.introFst(done))

            override def andThen[A, B, C](
              f: Arr[A, B],
              g: Arr[B, C],
            ): Arr[A, C] =
              dsl.andThen(
                dsl.andThen(f, dsl.snd(g)),
                dsl.andThen(dsl.assocRL, dsl.fst(join)),
              )

            override def par[A1, A2, B1, B2](
              f1: Arr[A1, B1],
              f2: Arr[A2, B2],
            ): Arr[A1 |*| A2, B1 |*| B2] =
              dsl.andThen(
                dsl.par(f1, f2),
                λ { case (d1 |*| b1) |*| (d2 |*| b2) =>
                  join(d1 |*| d2) |*| (b1 |*| b2)
                },
              )
          }

        val typeAlgebra: TypeAlgebra.Of[ScalaTypeParam, Arr, ConcreteType[T], |*|, One] =
          new TypeAlgebra[ScalaTypeParam, Arr] {
            override type Type = ConcreteType[T]
            override type <*>[A, B] = A |*| B
            override type None = One

            override def unit: Arr[One, ConcreteType[T]] =
              done > λ { case +(d) => d |*| ConcreteType.unit(d) }
            override def int: Arr[One, ConcreteType[T]] =
              done > λ { case +(d) => d |*| ConcreteType.int(d) }
            override def string: Arr[One, ConcreteType[T]] =
              done > λ { case +(d) => d |*| ConcreteType.string(d) }
            override def pair: Arr[ConcreteType[T] |*| ConcreteType[T], ConcreteType[T]] =
              λ { case t |*| u => constant(done) |*| ConcreteType.pair(t |*| u) }
            override def sum: Arr[ConcreteType[T] |*| ConcreteType[T], ConcreteType[T]] =
              λ { case t |*| u => constant(done) |*| ConcreteType.either(t |*| u) }
            override def recCall: Arr[ConcreteType[T] |*| ConcreteType[T], ConcreteType[T]] =
              λ { case t |*| u => constant(done) |*| ConcreteType.recCall(t |*| u) }
            override def fix(f: TypeFun[●, ●]): Arr[One, ConcreteType[T]] =
              // const(f) > ConcreteType.fix > introFst(done)
              ???
            override def abstractTypeName(name: ScalaTypeParam): Arr[One, ConcreteType[T]] =
              throw NotImplementedError(s"TODO (${summon[SourcePos]})")

            override given category: SymmetricMonoidalCategory[Arr, |*|, One] =
              compilationTarget.this.category
          }

        sealed trait as[K, Q]

        case object Map_○ extends as[○, One]
        case object Map_● extends as[●, ConcreteType[T]]
        case class Pair[K1, K2, Q1, Q2](
          f1: K1 as Q1,
          f2: K2 as Q2,
        ) extends as[K1 × K2, Q1 |*| Q2]

        given objectMap: MonoidalObjectMap[as, ×, ○, |*|, One] =
          new MonoidalObjectMap[as, ×, ○, |*|, One] {

            override def uniqueOutputType[A, B, C](f: as[A, B], g: as[A, C]): B =:= C =
              (f, g) match {
                case (Map_○, Map_○) => summon[B =:= C]
                case (Map_●, Map_●) => summon[B =:= C]
                case (Pair(f1, f2), Pair(g1, g2)) =>
                  (uniqueOutputType(f1, g1), uniqueOutputType(f2, g2)) match {
                    case (TypeEq(Refl()), TypeEq(Refl())) =>
                      summon[B =:= C]
                  }
              }

            override def pair[A1, A2, X1, X2](f1: as[A1, X1], f2: as[A2, X2]): as[A1 × A2, X1 |*| X2] =
              Pair(f1, f2)

            override def unpair[A1, A2, X](f: as[A1 × A2, X]): Unpaired[A1, A2, X] =
              f match {
                case Pair(f1, f2) => Unpaired.Impl(f1, f2)
              }

            override def unit: as[○, One] =
              Map_○
          }
      }

      def abstractify[T]: ConcreteType[ReboundType[T]] -⚬ TypeEmitter[T] = rec { self =>
        unpack > dsl.either(
          NonAbstractType.map(self) > TypeEmitter.nonAbstractType[T],
          λ { case label |*| nt =>
            val lbl1 |*| lbl2 = labels.split(labels.abstractify(label))
            val arg |*| resp = ReboundType.makeAbstractType[T](lbl1)
            returning(
              resp switch {
                case Left(x) =>
                  // (labels.neglect(lbl2) |*| x) :>> TypeEmitter.awaitPosFst[T]
                  val l = lbl2 :>> labels.alsoDebugPrint(s => s"Abstractification of $s returned a REFINEMENT")
                  (labels.neglect(l) |*| x) :>> TypeEmitter.awaitPosFst[T]
                case Right(value) =>
                  value switch {
                    case Left(inReq) =>
                      val l2 = lbl2 :>> labels.alsoDebugPrint(s => s"Abstractification of $s returned a Yield")
                      val res |*| resp = TypeEmitter.makeAbstractType[T](l2)
                      returning(
                        res,
                        resp switch {
                          case Left(y) =>
                            injectL(y) supplyTo inReq
                          case Right(value) =>
                            value switch {
                              case Left(outReq) =>
                                outReq.contramap(injectR) supplyTo inReq.contramap(injectR)
                              case Right(?(_)) =>
                                inReq :>> crashNow(s"TODO: eliminate? (${summon[SourcePos]})")
                            }
                        }
                      )
                    case Right(?(_)) =>
                      lbl2 :>> crashNow(s"TODO: eliminate? (${summon[SourcePos]})")
                  }
              },
              arg supplyTo nt,
            )
          },
        )
      }

      def mergeLower[T](
        splitT: T -⚬ (T |*| T),
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): (ConcreteType[ReboundType[T]] |*| ConcreteType[ReboundType[T]]) -⚬ TypeEmitter[T] =
        val abstractify = ConcreteType.abstractify[T]
        par(abstractify, abstractify) > TypeEmitter.merge(
          splitT,
          outputTParam,
        )

      def merge[T](
        splitT: T -⚬ (T |*| T),
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): (ConcreteType[ReboundType[T]] |*| ConcreteType[ReboundType[T]]) -⚬ ConcreteType[T] =
        val abstractify = ConcreteType.abstractify[T]
        par(abstractify, abstractify) > TypeEmitter.merge(
          splitT,
          outputTParam,
        ) > TypeEmitter.generify
        // rec { self =>
        //   par(unpack, unpack) > λ { case a |*| b =>
        //     a switch {
        //       case Left(a) =>
        //         b switch {
        //           case Left(b) =>
        //             (a |*| b) :>> NonAbstractType.merge(self, output) :>> nonAbstractType
        //           case Right(bLbl |*| u) =>
        //             val a1 |*| a2 = a :>> NonAbstractType.split(split)
        //             returning(
        //               nonAbstractType(a1),
        //               makeT(a2) supplyTo u,
        //             )
        //         }
        //       case Right(aLbl |*| nt) =>
        //         b switch {
        //           case Left(b) =>
        //             val b1 |*| b2 = b :>> NonAbstractType.split(split)
        //             returning(
        //               nonAbstractType(b1)
        //             )
        //           case Right(bLbl |*| nu) =>
        //             ???
        //         }
        //     }
        //   }
        // }

      def mergeTap[T](
        splitT: T -⚬ (T |*| T),
        splitTPreferred: T -⚬ (T |*| T),
        outletT: (TParamLabel |*| T) -⚬ ConcreteType[Done],
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): (ConcreteType[ReboundType[T]] |*| ConcreteType[ReboundType[T]]) -⚬ (TypeEmitter[T] |*| ConcreteType[Done]) =
        rec { self =>
          par(unpack, unpack) > λ { case a |*| b =>
            a switch {
              case Left(a) =>
                b switch {
                  case Left(b) =>
                    (a |*| b)
                      :>> NonAbstractType.mergeWith(self, output(???), output(???))
                      :>> NonAbstractType.splitMap(id)
                      :>> par(TypeEmitter.nonAbstractType, TypeOutlet.nonAbstractType)
                  case Right(bLbl |*| nb) =>
                    val b |*| (out1 |*| out2) =
                      a :>> NonAbstractType.splitMap(splitHPreferred1(splitT, splitTPreferred, outletT, outputT, outputTParam))
                        :>> snd(NonAbstractType.splitMap(id))
                    returning(
                      TypeEmitter.nonAbstractType(out1) |*| ConcreteType.nonAbstractType(out2),
                      ReboundType.nonAbstractType(b) supplyTo nb,
                    )
                }
              case Right(aLbl |*| na) =>
                b switch {
                  case Left(b) =>
                    val a |*| (out1 |*| out2) =
                      b :>> NonAbstractType.splitMap(splitHPreferred1(splitT, splitTPreferred, outletT, outputT, outputTParam))
                        :>> snd(NonAbstractType.splitMap(id))
                    returning(
                      TypeEmitter.nonAbstractType(out1) |*| TypeOutlet.nonAbstractType(out2),
                      ReboundType.nonAbstractType(a) supplyTo na,
                    )
                  case Right(bLbl |*| nb) =>
                    val t |*| o = labels.abstractify(bLbl) :>> TypeEmitter.abstractTypeOut(outletT)
                    val t1 |*| r = t :>> TypeEmitter.splitH(splitTPreferred, outputT, outputTParam)
                    val r1 |*| r2 = r :>> ReboundType.split(splitT, outputTParam)
                    returning(
                      t1 |*| o,
                      r1 supplyTo na,
                      r2 supplyTo nb,
                    )
                }
            }
          }
        }

      def mergeZap[T](
        splitT: T -⚬ (T |*| T),
        outletTParam: (TParamLabel |*| -[T]) -⚬ ConcreteType[Done],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): (ConcreteType[ReboundType[T]] |*| ConcreteType[ReboundType[T]]) -⚬ ConcreteType[Done] =
        rec { self =>
          par(unpack, unpack) > λ { case a |*| b =>
            a switch {
              case Left(a) =>
                b switch {
                  case Left(b) =>
                    (a |*| b)
                      :>> NonAbstractType.mergeWith(self, output(???), output(???))
                      :>> TypeOutlet.nonAbstractType
                  case Right(bLbl |*| nb) =>
                    val r |*| o = a :>> NonAbstractType.splitMap(splitOutPreferred1(splitT, outletTParam, outputTParam))
                    returning(
                      TypeOutlet.nonAbstractType(o),
                      ReboundType.nonAbstractType(r) supplyTo nb,
                    )
                }
              case Right(aLbl |*| na) =>
                b switch {
                  case Left(b) =>
                    val r |*| o = b :>> NonAbstractType.splitMap(splitOutPreferred1(splitT, outletTParam, outputTParam))
                    returning(
                      TypeOutlet.nonAbstractType(o),
                      ReboundType.nonAbstractType(r) supplyTo na,
                    )
                  case Right(bLbl |*| nb) =>
                    val r |*| o = labels.abstractify(aLbl) :>> ReboundType.abstractTypeOut(outletTParam)
                    val r1 |*| r2 = r :>> ReboundType.split(splitT, outputTParam)
                    returning(
                      o,
                      r1 supplyTo na,
                      r2 supplyTo nb,
                    )
                }
            }
          }
        }

      def mergeZap0[T](
        splitT: T -⚬ (T |*| T),
        // outletTParam: (TParamLabel |*| -[T]) -⚬ ConcreteType[Done],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): (ConcreteType[ReboundType[T]] |*| ConcreteType[ReboundType[T]]) -⚬ Val[Type] =
        rec { self =>
          par(unpack, unpack) > λ { case a |*| b =>
            a switch {
              case Left(a) =>
                b switch {
                  case Left(b) =>
                    (a |*| b)
                      :>> NonAbstractType.mergeWith(self, output(???), output(???))
                      // :>> TypeOutlet.nonAbstractType
                      :>> NonAbstractType.output(???)
                  case Right(bLbl |*| nb) =>
                    val r |*| o = a :>> NonAbstractType.splitMap(splitTapPreferred1(splitT, outputTParam))
                    returning(
                      // TypeOutlet.nonAbstractType(o),
                      NonAbstractType.output(???)(o),
                      ReboundType.nonAbstractType(r) supplyTo nb,
                    )
                }
              case Right(aLbl |*| na) =>
                b switch {
                  case Left(b) =>
                    val r |*| o = b :>> NonAbstractType.splitMap(splitTapPreferred1(splitT, outputTParam))
                    returning(
                      // TypeOutlet.nonAbstractType(o),
                      NonAbstractType.output(???)(o),
                      ReboundType.nonAbstractType(r) supplyTo na,
                    )
                  case Right(bLbl |*| nb) =>
                    // val r |*| o = labels.abstractify(aLbl) :>> ReboundType.abstractTypeOut(outletTParam)
                    val r |*| o = labels.abstractify(aLbl) :>> ReboundType.abstractTypeTap(outputTParam)
                    val r1 |*| r2 = r :>> ReboundType.split(splitT, outputTParam)
                    returning(
                      o,
                      r1 supplyTo na,
                      r2 supplyTo nb,
                    )
                }
            }
          }
        }

      def splitHPreferred1[T](
        splitT: T -⚬ (T |*| T),
        splitTPreferred: T -⚬ (T |*| T),
        outletT: (TParamLabel |*| T) -⚬ ConcreteType[Done],
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): ConcreteType[ReboundType[T]] -⚬ (ReboundType[T] |*| (TypeEmitter[T] |*| ConcreteType[Done])) =
        rec { self =>
          λ { t =>
            unpack(t) switch {
              case Left(t) =>
                val r |*| s = t :>> NonAbstractType.splitMap(self)
                val s1 |*| s2 = s :>> NonAbstractType.splitMap(id)
                ReboundType.nonAbstractType(r)
                  |*| (TypeEmitter.nonAbstractType(s1) |*| ConcreteType.nonAbstractType(s2))
              case Right(lbl |*| nt) =>
                val t |*| o = labels.abstractify(lbl) :>> TypeEmitter.abstractTypeOut[T](outletT)
                val t1 |*| r = t :>> TypeEmitter.splitH(splitTPreferred, outputT, outputTParam)
                val r1 |*| r2 = r :>> ReboundType.split(splitT, outputTParam)
                returning(
                  r2 |*| (t1 |*| o),
                  r1 supplyTo nt,
                )
            }
          }
        }

      def splitOutPreferred1[T](
        splitT: T -⚬ (T |*| T),
        outletTParam: (TParamLabel |*| -[T]) -⚬ ConcreteType[Done],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): ConcreteType[ReboundType[T]] -⚬ (ReboundType[T] |*| ConcreteType[Done]) =
        rec { self =>
          λ { t =>
            unpack(t) switch {
              case Left(t) =>
                val r |*| o = t :>> NonAbstractType.splitMap(self)
                ReboundType.nonAbstractType(r) |*| TypeOutlet.nonAbstractType(o)
              case Right(lbl |*| nt) =>
                val r |*| o = labels.abstractify(lbl) :>> ReboundType.abstractTypeOut[T](outletTParam)
                val r1 |*| r2 = r :>> ReboundType.split(splitT, outputTParam)
                returning(
                  r2 |*| o,
                  r1  supplyTo nt,
                )
            }
          }
        }

      def splitTapPreferred1[T](
        splitT: T -⚬ (T |*| T),
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): ConcreteType[ReboundType[T]] -⚬ (ReboundType[T] |*| Val[Type]) =
        rec { self =>
          λ { t =>
            unpack(t) switch {
              case Left(t) =>
                val r |*| o = t :>> NonAbstractType.splitMap(self)
                ReboundType.nonAbstractType(r) |*| NonAbstractType.output(???)(o)
              case Right(lbl |*| nt) =>
                val r |*| o = labels.abstractify(lbl) :>> ReboundType.abstractTypeTap[T](outputTParam)
                val r1 |*| r2 = r :>> ReboundType.split(splitT, outputTParam)
                returning(
                  r2 |*| o,
                  r1  supplyTo nt,
                )
            }
          }
        }

      def isPair[T]: ConcreteType[T] -⚬ (ConcreteType[T] |+| (ConcreteType[T] |*| ConcreteType[T])) =
        unpack > dsl.either(
          NonAbstractType.isPair > |+|.lmap(nonAbstractType),
          fst(labels.alsoDebugPrintTP(s => s"ABSTRACT TYPE $s was NOT a pair")) >
          typeParam > injectL,
        )

      def isRecCall[T]: ConcreteType[T] -⚬ (ConcreteType[T] |+| (ConcreteType[T] |*| ConcreteType[T])) =
        unpack > dsl.either(
          NonAbstractType.isRecCall > |+|.lmap(nonAbstractType),
          fst(labels.alsoDebugPrintTP(s => s"ABSTRACT TYPE $s was NOT a RecCall")) >
          typeParam > injectL,
        )

      // def degenerify[T](
      //   zeroTypeArg: TParamLabel -⚬ (T |*| Done),
      // ): GenericType[T] -⚬ DegenericType =
      //   rec { self =>
      //     unpack > dsl.either(
      //       NonAbstractType.map(self) > DegenericType.nonAbstractType,
      //       λ { case lbl |*| p =>
      //         val l1 |*| l2 = labels.dupTParam(lbl)
      //         val t |*| d = zeroTypeArg(l1)
      //         returning(
      //           DegenericType.abstractType(l2 waitFor d),
      //           t supplyTo p,
      //         )
      //       },
      //     )
      //   }

      def output[T](
        outputTypeParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): ConcreteType[T] -⚬ Val[Type] = rec { self =>
        λ { t =>
          unpack(t) switch {
            case Left(t)           => t :>> NonAbstractType.output(self)
            case Right(lbl |*| nt) => outputTypeParam(lbl |*| nt)
          }
        }
      }

      def debugPrintGradually[T](
        debugPrintTParam: (TParamLabel |*| -[T]) -⚬ Done,
      ): ConcreteType[T] -⚬ Done =
        λ { t =>
          unpack(t) switch {
            case Left(t) =>
              // XXX: not gradual
              t :>> crashNow(s"TODO (${summon[SourcePos]})")
            case Right(lbl |*| nt) =>
              debugPrintTParam(lbl |*| nt)
          }
        }

      def close[T](
        closeTParam: (TParamLabel |*| -[T]) -⚬ Done,
      ): ConcreteType[T] -⚬ Done = rec { self =>
        λ { t =>
          unpack(t) switch {
            case Left(t)           => t :>> NonAbstractType.close(self)
            case Right(lbl |*| nt) => closeTParam(lbl |*| nt)
          }
        }
      }

      given junctionConcreteType[T]: Junction.Positive[ConcreteType[T]] with {
        override def awaitPosFst: (Done |*| ConcreteType[T]) -⚬ ConcreteType[T] =
          rec { self =>
            λ { case d |*| a =>
              unpack(a) switch {
                case Left(t) =>
                  NonAbstractType.awaitPosFst(self)(d |*| t) :>> nonAbstractType
                case Right(lbl |*| t) =>
                  (lbl.waitFor(d) |*| t) :>> typeParam
              }
            }
          }
      }
    }

    object DegenericType {
      def pack: (NonAbstractTypeF[DegenericType] |+| Label) -⚬ DegenericType =
        dsl.pack[DegenericTypeF]

      def unpack: DegenericType -⚬ (NonAbstractTypeF[DegenericType] |+| Label) =
        dsl.unpack

      def nonAbstractType: NonAbstractTypeF[DegenericType] -⚬ DegenericType =
        injectL > pack

      def abstractedType: Label -⚬ DegenericType =
        injectR > pack

      // val output: DegenericType -⚬ Val[Type] = rec { self =>
      //   unpack > either(
      //     NonAbstractType.output(self),
      //     labels.toAbstractType,
      //   )
      // }

      // val neglect: DegenericType -⚬ Done =
      //   output > dsl.neglect
    }

    object TypeSkelet {
      def map[T, Y, X, Q](f: X -⚬ Q): TypeSkelet[T, Y, X] -⚬ TypeSkelet[T, Y, Q] =
        λ { t =>
          t switch {
            case Left(t)  => t :>> NonAbstractType.map(f) :>> injectL
            case Right(t) => t :>> snd(RefinementRequest.map(f)) :>> injectR
          }
        }

      def contramap[T, Y, X, P](f: P -⚬ Y): TypeSkelet[T, Y, X] -⚬ TypeSkelet[T, P, X] =
        λ { t =>
          t switch {
            case Left(t)  => t :>> injectL
            case Right(t) => t :>> snd(RefinementRequest.contramap(f)) :>> injectR
          }
        }

      def contramapT[T, Y, X, U](f: T -⚬ U): TypeSkelet[U, Y, X] -⚬ TypeSkelet[T, Y, X] =
        |+|.rmap(
          snd(RefinementRequest.contramapT(f))
        )

      def dimap[T, Y, X, P, Q](f: P -⚬ Y, g: X -⚬ Q): TypeSkelet[T, Y, X] -⚬ TypeSkelet[T, P, Q] =
        contramap(f) > map(g)

      def abstractType[T, Y, X]: (Label |*| -[ReboundF[T, Y, X]]) -⚬ TypeSkelet[T, Y, X] =
        injectR

      def makeAbstractType[T, Y, X]: Label -⚬ (TypeSkelet[T, Y, X] |*| ReboundF[T, Y, X]) =
        λ { lbl =>
          val req |*| resp = constant(demand[ReboundF[T, Y, X]])
          abstractType(lbl |*| req) |*| resp
        }

      def nonAbstractType[T, Y, X]: NonAbstractTypeF[X] -⚬ TypeSkelet[T, Y, X] =
        injectL

      def newAbstractType[T, Y, X](
        splitX: X -⚬ (X |*| X),
        mergeY: (Y |*| Y) -⚬ Y,
        tapFlop: Y -⚬ (Y |*| X),
        mergeT: (T |*| T) -⚬ T,
        outputY: Y -⚬ Val[Type],
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
      ): Label -⚬ (TypeSkelet[T, Y, X] |*| Val[Type] |*| TypeSkelet[T, Y, X]) =
        λ { lbl =>
          producing { case tl |*| t |*| tr =>
            ((abstractType[T, Y, X] >>: tl) |*| (abstractType[T, Y, X] >>: tr)) match {
              case (lblL |*| recvL) |*| (lblR |*| recvR) =>
                val lbl12 |*| lbl3 = labels.split(lbl)
                val lbl1 |*| lbl2 = labels.split(lbl12)
                returning(
                  lblL := lbl1,
                  lblR := lbl2,
                  t := Rebound.unifyRebounds(
                    splitX,
                    mergeY,
                    tapFlop,
                    mergeT,
                  )(recvL.asInput |*| recvR.asInput) switch {
                    case Left(y) =>
                      outputY(y) waitFor labels.neglect(lbl3)
                    case Right(yld) =>
                      yld switch {
                        case Left(req) =>
                          val --(t) = req contramap injectR
                          outputT(labels.generify(lbl3) |*| t)
                        case Right(?(_)) =>
                          lbl3 :>> crashNow(s"TODO: eliminate this case (at ${summon[SourcePos]})")
                      }
                  },
                )
            }
          }
        }

      def await[T, Y, X](
        awaitX: X -⚬ (NonAbstractTypeF[X] |+| (Label |*| -[T])),
      ): TypeSkelet[T, Y, X] -⚬ (NonAbstractTypeF[X] |+| (Label |*| -[T])) =
        λ { t =>
          t switch {
            case Left(t) =>
              injectL(t)
            case Right(lbl |*| req) =>
              RefinementRequest.decline(req) switch {
                case Left(x) => awaitX(x)
                case Right(t) => injectR(lbl |*| t)
              }
          }
        }

      def split[T, Y, X](
        splitX: X -⚬ (X |*| X),
        mergeY: (Y |*| Y) -⚬ Y,
        tapFlop: Y -⚬ (Y |*| X),
        mergeT: (T |*| T) -⚬ T,
      ): TypeSkelet[T, Y, X] -⚬ (TypeSkelet[T, Y, X] |*| TypeSkelet[T, Y, X]) =
        λ { t =>
          t switch {
            case Right(lbl |*| req) => // abstract type
              val l1 |*| l2 = labels.split(lbl)
              val r1 |*| r2 = req :>> RefinementRequest.split(splitX, mergeY, tapFlop, mergeT)
              abstractType(l1 |*| r1) |*| abstractType(l2 |*| r2)
            case Left(t) =>
              t :>> NonAbstractType.split(splitX) :>> par(nonAbstractType, nonAbstractType)
          }
        }

      def splitPreferred[T, Y, X](
        splitXPreferred: X -⚬ (X |*| X),
        splitYH: Y -⚬ (Y |*| X),
        splitYHPreferred1: Y -⚬ (Y |*| X),
        mergeTPreferred: (T |*| T) -⚬ T,
        makeX: TypeSkelet[T, Y, X] -⚬ X,
      ): TypeSkelet[T, Y, X] -⚬ (X |*| X) =
        λ { t =>
          t switch {
            case Left(t) =>
              t :>> NonAbstractType.split(splitXPreferred) :>> par(nonAbstractType > makeX, nonAbstractType > makeX)
            case Right(lbl |*| req) => // abstract type
              val l1 |*| l2 = labels.split(lbl)
              val out1 |*| resp1 = l1 :>> makeAbstractType[T, Y, X]
              makeX(out1) |*| (resp1 switch {
                case Left(y) =>
                  val y0 |*| x2 = splitYHPreferred1(y)
                  returning(x2, RefinementRequest.completeWith(req |*| y0))
                case Right(value) =>
                  value switch {
                    case Left(req1) =>
                      val out2 |*| resp2 = l2 :>> makeAbstractType[T, Y, X]
                      returning(
                        makeX(out2),
                        resp2 switch {
                          case Left(y) =>
                            val y0 |*| x1 = splitYH(y)
                            returning(
                              RefinementRequest.completeWith(req |*| y0),
                              injectL(x1) supplyTo req1,
                            )
                          case Right(value) =>
                            value switch {
                              case Left(req2) =>
                                RefinementRequest.decline(req) switch {
                                  case Left(x) =>
                                    val x1 |*| x2 = splitXPreferred(x)
                                    returning(
                                      injectL(x1) supplyTo req1,
                                      injectL(x2) supplyTo req2,
                                    )
                                  case Right(nt) =>
                                    val --(t1) = req1 :>> contrapositive(injectR)
                                    val --(t2) = req2 :>> contrapositive(injectR)
                                    mergeTPreferred(t1 |*| t2) supplyTo nt
                                }
                              case Right(?(_)) =>
                                constant(crashNow(s"TODO: Eliminate (at ${summon[SourcePos]})"))
                            }
                        },
                      )
                    case Right(?(_)) =>
                      l2 :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
                  }
              })
          }
        }

      def splitH[T, Y, X](
        splitH: X -⚬ (X |*| Y),
        mergeYX: (Y |*| X) -⚬ Y,
        splitYPreferred: Y -⚬ (Y |*| Y),
        splitXYPreferred: X -⚬ (X |*| Y),
        splitTPreferred: T -⚬ (T |*| T),
      ): TypeSkelet[T, Y, X] -⚬ (TypeSkelet[T, Y, X] |*| TypeSkelet[-[T], X, Y]) =
        λ { t =>
          t switch {
            case Left(t) =>
              t :>> NonAbstractType.splitMap(splitH) :>> par(
                nonAbstractType,
                nonAbstractType,
              )
            case Right(label |*| req) =>
              val l1 |*| l2 = labels.split(label)
              val req1 |*| req2 = req :>> RefinementRequest.splitH(splitH, mergeYX, splitYPreferred, splitXYPreferred, splitTPreferred)
              abstractType(l1 |*| req1) |*| abstractType(l2 |*| req2)
          }
        }

      def splitHPreferred1[T, Y, X](
        splitH: X -⚬ (X |*| Y),
        splitHPreferred1: X -⚬ (X |*| Y),
        splitYPreferred: Y -⚬ (Y |*| Y),
        makeX: TypeSkelet[T, Y, X] -⚬ X,
        makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
        splitTPreferred: T -⚬ (T |*| T),
      ): TypeSkelet[T, Y, X] -⚬ (X |*| Y) =
        λ { t =>
          t switch {
            case Left(t) =>
              t :>> NonAbstractType.splitMap(splitHPreferred1) :>> par(
                nonAbstractType > makeX,
                nonAbstractType > makeY,
              )
            case Right(label |*| req) =>
              val out1 |*| resp1 = label :>> makeAbstractType[T, Y, X]
              makeX(out1) |*| (resp1 switch {
                case Left(y) =>
                  val y1 |*| y2 = splitYPreferred(y)
                  returning(
                    y2,
                    RefinementRequest.completeWith(req |*| y1),
                  )
                case Right(value) =>
                  value switch {
                    case Left(req1) =>
                      val out2 |*| resp2 = label :>> makeAbstractType[-[T], X, Y]
                      returning(
                        makeY(out2),
                        resp2 switch {
                          case Left(x) =>
                            val x1 |*| y = splitH(x)
                            returning(
                              RefinementRequest.completeWith(req |*| y),
                              injectL(x1) supplyTo req1,
                            )
                          case Right(req2) =>
                            req2 switch {
                              case Left(req2) =>
                                RefinementRequest.decline(req) switch {
                                  case Left(x) =>
                                    val x1 |*| y2 = splitHPreferred1(x)
                                    returning(
                                      injectL(x1) supplyTo req1,
                                      injectL(y2) supplyTo req2,
                                    )
                                  case Right(nt) =>
                                    val --(t)   = req1 :>> contrapositive(injectR)
                                    val --(nt2) = req2 :>> contrapositive(injectR)
                                    val t1 |*| t2 = splitTPreferred(t)
                                    returning(
                                      t1 supplyTo nt,
                                      t2 supplyTo nt2,
                                    )
                                }
                              case Right(?(_)) =>
                                ???
                            }
                        },
                      )
                    case Right(?(_)) =>
                      ???
                  }
              })
          }
        }

      def mergeOp[T, Y, X](
        splitX: X -⚬ (X |*| X),
        makeX: TypeSkelet[T, Y, X] -⚬ X,
        makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
        tapFlop: Y -⚬ (Y |*| X),
        mergeY: (Y |*| Y) -⚬ Y,
        outputYApprox: Y -⚬ Val[Type],
        mergeT: (T |*| T) -⚬ T,
        outputTParam: (TParamLabel |*| T) -⚬ Val[Type],
      )(using
        Junction.Positive[X],
        Junction.Positive[Y],
        Junction.Positive[T],
      ): (TypeSkelet[-[T], X, Y] |*| TypeSkelet[-[T], X, Y]) -⚬ Y = {
        import NonAbstractType.junctionNonAbstractType

        λ { case a |*| b =>
          a switch {
            case Right(aLabel |*| aReq) => // `a` is abstract type
              b switch {
                case Right(bLabel |*| bReq) => // `b` is abstract type
                  labels.compare(aLabel |*| bLabel) switch {
                    case Left(label) => // labels are same => neither refines the other
                      val lbl1 |*| lbl2 = labels.split(label)
                      val res |*| resp = makeAbstractType[-[T], X, Y](lbl1)
                      returning(
                        makeY(res),
                        resp switch {
                          case Left(x) =>
                            val x1 |*| x2 = splitX(x waitFor labels.neglect(lbl2))
                            returning(
                              injectL(x1) supplyTo aReq,
                              injectL(x2) supplyTo bReq,
                            )
                          case Right(value) =>
                            value switch {
                              case Left(outReq) =>
                                val a = RefinementRequest.decline(aReq)
                                val b = RefinementRequest.decline(bReq)
                                a switch {
                                  case Left(y1) =>
                                    b switch {
                                      case Left(y2) =>
                                        injectL(mergeY(y1 |*| y2) waitFor labels.neglect(lbl2)) supplyTo outReq
                                      case Right(--(t2)) =>
                                        val l1 |*| l2 = labels.split(lbl2)
                                        val d = (labels.show(l1) ** outputYApprox(y1) ** outputTParam(labels.generify(l2) |*| t2)) :>> printLine { case ((l, y1), t2) =>
                                          s"label = $l, y1 = $y1, t2 = $t2"
                                        }
                                        (d |*| outReq) :>> crashWhenDone(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
                                    }
                                  case Right(--(t1)) =>
                                    b switch {
                                      case Left(y2) =>
                                        (t1 |*| (y2 waitFor labels.neglect(lbl2)) |*| outReq) :>> crashNow(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
                                      case Right(--(t2)) =>
                                        injectR(dii(mergeT(t1 |*| t2) waitFor labels.neglect(lbl2))) supplyTo outReq
                                    }
                                }
                              case Right(?(_)) =>
                                (lbl2 |*| aReq |*| bReq) :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
                            }
                        }
                      )
                    case Right(res) =>
                      val go: (Label |*| RefinementRequestF[-[T], X, Y] |*| RefinementRequestF[-[T], X, Y]) -⚬ Y =
                        λ { case label |*| req1 |*| req2 =>
                          val lbl1 |*| lbl2 = labels.split(label)
                          val x |*| resp = makeAbstractType[T, Y, X](lbl1)
                          returning(
                            resp switch {
                              case Left(y) =>
                                val y1 |*| x1 = tapFlop(y)
                                returning(
                                  y1 waitFor labels.neglect(lbl2),
                                  RefinementRequest.completeWith(req1 |*| x1),
                                )
                              case Right(value) =>
                                value switch {
                                  case Left(req2) =>
                                    val out |*| resp = makeAbstractType[-[T], X, Y](lbl2)
                                    returning(
                                      makeY(out),
                                      resp switch {
                                        case Left(x) =>
                                          val x1 |*| x2 = splitX(x)
                                          returning(
                                            RefinementRequest.completeWith(req1 |*| x1),
                                            injectL(x2) supplyTo req2,
                                          )
                                        case Right(value) =>
                                          value switch {
                                            case Left(outReq) =>
                                              RefinementRequest.decline(req1) switch {
                                                case Left(y) =>
                                                  val y1 |*| x1 = tapFlop(y)
                                                  returning(
                                                    injectL(y1) supplyTo outReq,
                                                    injectL(x1) supplyTo req2,
                                                  )
                                                case Right(--(t1)) =>
                                                  val --(t2) = req2 contramap injectR
                                                  injectR(dii(mergeT(t1 |*| t2))) supplyTo outReq
                                              }
                                            case Right(?(_)) =>
                                              (req1 |*| req2) :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
                                          }
                                      }
                                    )
                                  case Right(?(_)) =>
                                    (lbl2 |*| req1) :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
                                }
                            },
                            RefinementRequest.completeWith(req2 |*| makeX(x)),
                          )
                        }

                      res switch {
                        case Left(aLabel) =>
                          go(aLabel |*| aReq |*| bReq)
                        case Right(bLabel) =>
                          go(bLabel |*| bReq |*| aReq)
                      }
                  }
                case Left(b) => // `b` is not abstract type
                  val y |*| x = b :>> NonAbstractType.splitMap(tapFlop)
                  returning(
                    makeY(nonAbstractType(y waitFor labels.neglect(aLabel))),
                    RefinementRequest.completeWith(aReq |*| makeX(nonAbstractType(x))),
                  )
              }
            case Left(a) => // `a` is not abstract type
              b switch {
                case Right(bLabel |*| bReq) => // `b` is abstract type
                  val y |*| x = a :>> NonAbstractType.splitMap(tapFlop)
                  returning(
                    makeY(nonAbstractType(y waitFor labels.neglect(bLabel))),
                    RefinementRequest.completeWith(bReq |*| makeX(nonAbstractType(x))),
                  )
                case Left(b) => // `b` is not abstract type
                  makeY(nonAbstractType(NonAbstractType.merge(mergeY, outputYApprox)(a |*| b)))
              }
          }
        }
      }

      def merge[T, Y, X](
        mergeX: (X |*| X) -⚬ X,
        splitY: Y -⚬ (Y |*| Y),
        tapFlipXY: X -⚬ (X |*| Y),
        makeX: TypeSkelet[  T , Y, X] -⚬ X,
        makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
        splitT: T -⚬ (T |*| T),
        outputXApprox: X -⚬ Val[Type],
      )(using
        Junction.Positive[X],
      ): (TypeSkelet[T, Y, X] |*| TypeSkelet[T, Y, X]) -⚬ X =
        λ { case a |*| b =>
          a switch {
            case Right(aLabel |*| aReq) => // `a` is abstract type
              b switch {
                case Right(bLabel |*| bReq) => // `b` is abstract type
                  mergeAbstractTypes(mergeX, splitY, tapFlipXY, makeX, makeY, splitT)(
                    (aLabel |*| aReq) |*| (bLabel |*| bReq)
                  )
                case Left(b) => // `b` is not abstract type
                  import NonAbstractType.junctionNonAbstractType
                  val bx |*| by = b :>> NonAbstractType.splitMap[X, X, Y](tapFlipXY)
                  returning(
                    makeX(nonAbstractType(bx waitFor labels.neglect(aLabel))),
                    RefinementRequest.completeWith(aReq |*| makeY(nonAbstractType(by))),
                  )
              }
            case Left(a) => // `a` is not abstract type
              b switch {
                case Right(bLabel |*| bReq) => // `b` is abstract type
                  val ax |*| ay = a :>> NonAbstractType.splitMap[X, X, Y](tapFlipXY)
                  returning(
                    makeX(nonAbstractType[T, Y, X](ax)) waitFor labels.neglect(bLabel),
                    RefinementRequest.completeWith(bReq |*| makeY(nonAbstractType(ay))),
                  )
                case Left(b) => // `b` is not abstract type
                  makeX(nonAbstractType((a |*| b) :>> NonAbstractType.merge(mergeX, outputXApprox)))
              }
          }
        }

      def mergeAbstractTypes[T, Y, X](
        mergeX: (X |*| X) -⚬ X,
        splitY: Y -⚬ (Y |*| Y),
        tapFlipXY: X -⚬ (X |*| Y),
        makeX: TypeSkelet[  T , Y, X] -⚬ X,
        makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
        splitT: T -⚬ (T |*| T),
      )(using
        Junction.Positive[X],
      ): ((Label |*| RefinementRequestF[T, Y, X]) |*| (Label |*| RefinementRequestF[T, Y, X])) -⚬ X =
        λ { case (aLabel |*| aReq) |*| (bLabel |*| bReq) =>
          labels.compare(aLabel |*| bLabel) switch {
            case Left(label) => // labels are same => neither refines the other
              val x |*| resp = makeAbstractType[T, Y, X](label)
              returning(
                makeX(x),
                resp switch {
                  case Left(y) =>
                    val y1 |*| y2 = splitY(y)
                    returning(
                      RefinementRequest.completeWith(aReq |*| y1),
                      RefinementRequest.completeWith(bReq |*| y2),
                    )
                  case Right(value) =>
                    value switch {
                      case Left(outReq) =>
                        val a = RefinementRequest.decline(aReq)
                        val b = RefinementRequest.decline(bReq)
                        a switch {
                          case Left(x1) =>
                            b switch {
                              case Left(x2) =>
                                injectL(mergeX(x1 |*| x2)) supplyTo outReq
                              case Right(nt) =>
                                (x1 |*| nt |*| outReq) :>> crashNow(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
                            }
                          case Right(nt1) =>
                            b switch {
                              case Left(x2) =>
                                (x2 |*| nt1 |*| outReq) :>> crashNow(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
                              case Right(nt2) =>
                                val --(t) = outReq contramap injectR
                                val t1 |*| t2 = splitT(t)
                                returning(
                                  t1 supplyTo nt1,
                                  t2 supplyTo nt2,
                                )
                            }
                        }
                      case Right(?(_)) =>
                        (aReq |*| bReq) :>> crashNow(s"TODO: eliminate impossible case (${summon[SourcePos]})")
                    }
                },
              )
            case Right(res) =>
              def go: (Label |*| RefinementRequestF[T, Y, X] |*| RefinementRequestF[T, Y, X]) -⚬ X =
                λ { case aLabel |*| aReq |*| bReq =>
                  val aLbl1 |*| aLbl2 = labels.split(aLabel)
                  val y |*| resp = makeAbstractType[-[T], X, Y](aLbl1)
                  returning(
                    resp switch {
                      case Left(x) =>
                        val x1 |*| y1 = tapFlipXY(x)
                        returning(
                          x1 waitFor labels.neglect(aLbl2),
                          RefinementRequest.completeWith(aReq |*| y1),
                        )
                      case Right(b) =>
                        b switch {
                          case Right(?(_)) =>
                            (aLbl2 |*| aReq) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
                          case Left(bReq1) =>
                            val x |*| resp = makeAbstractType[T, Y, X](aLbl2)
                            returning(
                              makeX(x),
                              resp switch {
                                case Left(y) =>
                                  val y1 |*| y2 = splitY(y)
                                  returning(
                                    RefinementRequest.completeWith(aReq |*| y1),
                                    injectL(y2) supplyTo bReq1,
                                  )
                                case Right(value) =>
                                  value switch {
                                    case Right(?(_)) =>
                                      (aReq |*| bReq1) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
                                    case Left(outReq) =>
                                      RefinementRequest.decline(aReq) switch {
                                        case Left(res) =>
                                          val x1 |*| y1 = tapFlipXY(res)
                                          returning(
                                            injectL(x1) supplyTo outReq,
                                            injectL(y1) supplyTo bReq1,
                                          )
                                        case Right(nt) =>
                                          val --(nt1) = bReq1 contramap injectR
                                          val --(t) = outReq contramap injectR
                                          val (t1 |*| t2) = splitT(t)
                                          returning(
                                            t1 supplyTo nt,
                                            t2 supplyTo nt1,
                                          )
                                      }
                                  }
                              }
                            )
                        }
                    },
                    RefinementRequest.completeWith(bReq |*| makeY(y)),
                  )
                }

              res switch {
                case Left(aLabel) =>
                  go(aLabel |*| aReq |*| bReq)
                case Right(bLabel) =>
                  go(bLabel |*| bReq |*| aReq)
              }
          }
        }
      def mergeH[T, Y, X](
        mergeXY: (X |*| Y) -⚬ X,
        splitYX: Y -⚬ (Y |*| X),
        splitXPreferred: X -⚬ (X |*| X),
        splitYXPreferred1: Y -⚬ (Y |*| X),
        makeX: TypeSkelet[  T , Y, X] -⚬ X,
        makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
        outputXApprox: X -⚬ Val[Type],
        outputYApprox: Y -⚬ Val[Type],
        mergeTPreferred: (T |*| T) -⚬ T,
      ): (TypeSkelet[T, Y, X] |*| TypeSkelet[-[T], X, Y]) -⚬ X =
        λ { case a |*| b =>
          a switch {
            case Left(a) =>
              b switch {
                case Left(b) =>
                  (a |*| b) :>> NonAbstractType.mergeWith(mergeXY, outputXApprox, outputYApprox) > nonAbstractType > makeX
                case Right(bLbl |*| bReq) =>
                  val x2 |*| xOut = a :>> NonAbstractType.splitMap(splitXPreferred) :>> par(nonAbstractType[T, Y, X], nonAbstractType[T, Y, X])
                  returning(makeX(xOut), RefinementRequest.completeWith(bReq |*| makeX(x2)))
              }
            case Right(aLbl |*| aReq) =>
              b switch {
                case Left(b) =>
                  val y1 |*| xOut = b :>> NonAbstractType.splitMap(splitYXPreferred1) :>> par(nonAbstractType[-[T], X, Y], nonAbstractType[T, Y, X])
                  returning(makeX(xOut), RefinementRequest.completeWith(aReq |*| makeY(y1)))
                case Right(bLbl |*| bReq) =>
                  ((aLbl |*| aReq) |*| (bLbl |*| bReq)) :>> mergeHAbstractTypes[T, Y, X](
                    splitXPreferred,
                    splitYX,
                    splitYXPreferred1,
                    mergeXY,
                    makeX,
                    makeY,
                    mergeTPreferred,
                  )
              }
          }
        }

      def mergeHAbstractTypes[T, Y, X](
        splitXPreferred: X -⚬ (X |*| X),
        splitYX: Y -⚬ (Y |*| X),
        splitYXPreferred1: Y -⚬ (Y |*| X),
        mergeXY: (X |*| Y) -⚬ X,
        makeX: TypeSkelet[  T , Y, X] -⚬ X,
        makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
        mergeTPreferred: (T |*| T) -⚬ T,
      ): ((Label |*| RefinementRequestF[T, Y, X]) |*| (Label |*| RefinementRequestF[-[T], X, Y])) -⚬ X = {
        λ { case (aLbl |*| aReq) |*| (bLbl |*| bReq) =>
          labels.compare(aLbl |*| bLbl) switch {
            case Left(lbl) => // labels are same, neither refines the other
              val out |*| resp = makeAbstractType[T, Y, X](lbl)
              returning(
                makeX(out),
                resp switch {
                  case Left(y) =>
                    val y1 |*| x2 = splitYX(y)
                    returning(
                      RefinementRequest.completeWith(aReq |*| y1),
                      RefinementRequest.completeWith(bReq |*| x2),
                    )
                  case Right(value) =>
                    value switch {
                      case Left(req) =>
                        val a = RefinementRequest.decline(aReq)
                        val b = RefinementRequest.decline(bReq)
                        a switch {
                          case Left(x) =>
                            b switch {
                              case Left(y) =>
                                injectL(mergeXY(x |*| y)) supplyTo req
                              case Right(--(t)) =>
                                (req |*| x |*| t) :>> crashNow(s"The same abstract type resolve to 2 different outcomes (at ${summon[SourcePos]})")
                            }
                          case Right(nt) =>
                            b switch {
                              case Left(y) =>
                                (req |*| y |*| nt) :>> crashNow(s"The same abstract type resolve to 2 different outcomes (at ${summon[SourcePos]})")
                              case Right(--(t2)) =>
                                val --(tOut) = req :>> contrapositive(injectR)
                                mergeTPreferred(t2 |*| tOut) supplyTo nt
                            }
                        }
                      case Right(?(_)) =>
                        constant(crashNow(s"TODO: eliminate (at ${summon[SourcePos]})"))
                    }
                },
              )
            case Right(res) =>
              res switch {
                case Left(aLbl) =>
                  val x2 |*| resp2 = aLbl :>> makeAbstractType[T, Y, X]
                  returning(
                    resp2 switch {
                      case Left(y) =>
                        mergeXY(makeX(abstractType(aLbl |*| aReq)) |*| y)
                      case Right(value) =>
                        value switch {
                          case Left(req2) =>
                            val out |*| resp = aLbl :>> makeAbstractType[T, Y, X]
                            returning(
                              makeX(out),
                              resp switch {
                                case Left(y) =>
                                  val y1 |*| x2 = splitYX(y)
                                  returning(
                                    RefinementRequest.completeWith(aReq |*| y1),
                                    injectL(x2) supplyTo req2,
                                  )
                                case Right(value) =>
                                  value switch {
                                    case Left(req) =>
                                      RefinementRequest.decline(aReq) switch {
                                        case Left(x) =>
                                          val x2 |*| xOut = splitXPreferred(x)
                                          returning(
                                            injectL(x2) supplyTo req2,
                                            injectL(xOut) supplyTo req,
                                          )
                                        case Right(nt) =>
                                          val --(t2)   = req2 :>> contrapositive(injectR)
                                          val --(tOut) = req  :>> contrapositive(injectR)
                                          mergeTPreferred(t2 |*| tOut) supplyTo nt
                                      }
                                    case Right(?(_)) =>
                                      constant(crashNow(s"TODO: eliminate (at ${summon[SourcePos]})"))
                                  }
                              }
                            )
                          case Right(?(_)) =>
                            constant(crashNow(s"TODO: eliminate (at ${summon[SourcePos]})"))
                        }
                    },
                    RefinementRequest.completeWith(bReq |*| makeX(x2)),
                  )
                case Right(bLbl) =>
                  val y1 |*| resp1 = bLbl :>> makeAbstractType[-[T], X, Y]
                  returning(
                    resp1 switch {
                      case Left(x) =>
                        mergeXY(x |*| makeY(abstractType(bLbl |*| bReq)))
                      case Right(value) =>
                        value switch {
                          case Left(req1) =>
                            val out |*| resp = bLbl :>> makeAbstractType[T, Y, X]
                            returning(
                              makeX(out),
                              resp switch {
                                case Left(y) =>
                                  val y1 |*| x2 = splitYX(y)
                                  returning(
                                    injectL(y1) supplyTo req1,
                                    RefinementRequest.completeWith(bReq |*| x2),
                                  )
                                case Right(value) =>
                                  value switch {
                                    case Left(req) =>
                                      RefinementRequest.decline(bReq) switch {
                                        case Left(y) =>
                                          val y1 |*| xOut = splitYXPreferred1(y)
                                          returning(
                                            injectL(y1) supplyTo req1,
                                            injectL(xOut) supplyTo req,
                                          )
                                        case Right(--(t2)) =>
                                          val --(nt)   = req1 :>> contrapositive(injectR)
                                          val --(tOut) = req  :>> contrapositive(injectR)
                                          mergeTPreferred(t2 |*| tOut) supplyTo nt
                                      }
                                    case Right(?(_)) =>
                                      constant(crashNow(s"TODO: eliminate (at ${summon[SourcePos]})"))
                                  }
                              }
                            )
                          case Right(?(_)) =>
                            constant(crashNow(s"TODO: eliminate (at ${summon[SourcePos]})"))
                        }
                    },
                    RefinementRequest.completeWith(aReq |*| makeY(y1)),
                  )
              }
          }
        }
      }

      def tapFlop[T, Y, X](
        splitX: X -⚬ (X |*| X),
        tapFlop: Y -⚬ (Y |*| X),
        makeX: TypeSkelet[T, Y, X] -⚬ X,
        makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
        mergeT: (T |*| T) -⚬ T,
      )(using
        Junction.Positive[X],
      ): TypeSkelet[-[T], X, Y] -⚬ (Y |*| X) =
        λ { t =>
          t switch {
            case Right(label |*| req) =>
              val lbl1 |*| lbl2 = labels.split(label)
              val (out2 |*| resp2) = makeAbstractType[T, Y, X](lbl1)
              val out1 = resp2 switch {
                case Left(y) =>
                  val y1 |*| x1 = tapFlop(y)
                  returning(
                    y1,
                    RefinementRequest.completeWith(req |*| (x1 waitFor labels.neglect(lbl2)))
                  )
                case Right(value) =>
                  value switch {
                    case Left(outReq2) =>
                      val (out1 |*| resp1) = makeAbstractType[-[T], X, Y](lbl2)
                      returning(
                        makeY(out1),
                        resp1 switch {
                          case Left(x) =>
                            val x1 |*| x2 = splitX(x)
                            returning(
                              RefinementRequest.completeWith(req |*| x1),
                              injectL(x2) supplyTo outReq2,
                            )
                          case Right(value) =>
                            value switch {
                              case Left(outReq1) =>
                                RefinementRequest.decline(req) switch {
                                  case Left(y) =>
                                    val y1 |*| x1 = tapFlop(y)
                                    returning(
                                      injectL(y1) supplyTo outReq1,
                                      injectL(x1) supplyTo outReq2,
                                    )
                                  case Right(--(t1)) =>
                                    val --(t2) = outReq2 contramap injectR
                                    val t = mergeT(t1 |*| t2)
                                    injectR(dii(t)) supplyTo outReq1
                                }
                              case Right(?(_)) =>
                                (outReq2 |*| req) :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
                            }
                        },
                      )
                    case Right(?(_)) =>
                      (lbl2 |*| req) :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
                  }
              }
              out1 |*| makeX(out2)
            case Left(a) => // NonAbstractType
              a :>> NonAbstractType.splitMap[Y, Y, X](tapFlop) :>> par(
                nonAbstractType > makeY,
                nonAbstractType > makeX,
              )
          }
        }

      def tapFlip[T, Y, X](
        splitY: Y -⚬ (Y |*| Y),
        tapFlip: X -⚬ (X |*| Y),
        makeX: TypeSkelet[  T , Y, X] -⚬ X,
        makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
        splitT: T -⚬ (T |*| T),
      )(using
        Junction.Positive[X],
      ): TypeSkelet[T, Y, X] -⚬ (X |*| Y) =
        λ { t =>
          t switch {
            case Right(label |*| req) => // abstract type
              val lbl1 |*| lbl2 = labels.split(label)
              val out2 |*| resp2 = makeAbstractType[-[T], X, Y](lbl1)
              val out1 = resp2 switch {
                case Left(x) =>
                  val x1 |*| y1 = tapFlip(x)
                  returning(
                    x1 waitFor labels.neglect(lbl2),
                    RefinementRequest.completeWith(req |*| y1),
                  )
                case Right(value) =>
                  value switch {
                    case Left(outReq2) =>
                      val out1 |*| resp1 = makeAbstractType[T, Y, X](lbl2)
                      returning(
                        makeX(out1),
                        resp1 switch {
                          case Left(y) =>
                            val y1 |*| y2 = splitY(y)
                            returning(
                              RefinementRequest.completeWith(req |*| y1),
                              injectL(y2) supplyTo outReq2,
                            )
                          case Right(value) =>
                            value switch {
                              case Left(outReq1) =>
                                RefinementRequest.decline(req) switch {
                                  case Left(x) =>
                                    val x1 |*| y1 = tapFlip(x)
                                    returning(
                                      injectL(x1) supplyTo outReq1,
                                      injectL(y1) supplyTo outReq2,
                                    )
                                  case Right(nt) =>
                                    val --(t) = outReq1 contramap injectR
                                    val t1 |*| t2 = splitT(t)
                                    returning(
                                      t1 supplyTo nt,
                                      injectR(dii(t2)) supplyTo outReq2,
                                    )
                                }
                              case Right(?(_)) =>
                                (outReq2 |*| req) :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
                            }
                        }
                      )
                    case Right(?(_)) =>
                      (lbl2 |*| req) :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
                  }
              }
              out1 |*| makeY(out2)
            case Left(t) => // non-abstract type
              t :>> NonAbstractType.splitMap[X, X, Y](tapFlip) :>> par(
                nonAbstractType > makeX,
                nonAbstractType > makeY,
              )
          }
        }

      def output[T, Y, X](
        outputX: X -⚬ Val[Type],
        outputNegT: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): TypeSkelet[T, Y, X] -⚬ Val[Type] =
        λ { _ switch {
          case Right(label |*| req) => // abstract type
            RefinementRequest.decline(req) switch {
              case Left(x)   => outputX(x) waitFor labels.neglect(label)
              case Right(nt) => outputNegT(labels.generify(label) |*| nt)
            }
          case Left(x) =>
            NonAbstractType.output(outputX)(x)
        }}

      def close[T, Y, X](
        neglectX: X -⚬ Done,
        closeTParam: (TParamLabel |*| -[T]) -⚬ Done,
      ): TypeSkelet[T, Y, X] -⚬ Done =
        λ { _ switch {
          case Right(label |*| req) => // abstract type
            RefinementRequest.decline(req) switch {
              case Left(x)   =>
                join(neglectX(x) |*| labels.neglect(label))
              case Right(nt) =>
                closeTParam(labels.generify(label) |*| nt)
            }
          case Left(x) =>
            NonAbstractType.close(neglectX)(x)
        }}

      def outputApprox[T, Y, X](
        outputXApprox: X -⚬ Val[Type],
        outputTParamApprox: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): TypeSkelet[T, Y, X] -⚬ Val[Type] =
        λ { _ switch {
          case Right(label |*| req) => // abstract type
            RefinementRequest.decline(req) switch {
              case Left(x) =>
                outputXApprox(x)
                  .waitFor(labels.neglect(label))
              case Right(nt) =>
                outputTParamApprox(labels.generify(label) |*| nt)
            }
          case Left(x) =>
            NonAbstractType.output(outputXApprox)(x)
        }}

      def outlet[T, Y, X](
        // f: X -⚬ TypeOutlet[Done],
        f: X -⚬ ConcreteType[Done],
        // outletTParam: (TParamLabel |*| -[T]) -⚬ TypeOutlet[Done],
        outletTParam: (TParamLabel |*| -[T]) -⚬ ConcreteType[Done],
      ): TypeSkelet[T, Y, X] -⚬ ConcreteType[Done] =
        dsl.either(
          λ { x => ConcreteType.nonAbstractType(NonAbstractType.map(f)(x)) },
          λ { case lbl |*| req =>
            RefinementRequest.decline(req) switch {
              case Left(x) =>
                f(x)
              case Right(nt) =>
                outletTParam(labels.generify(lbl) |*| nt)
            }
          },
        )

      def generify[T, Y, X](
        wrapX: X -⚬ ConcreteType[T],
      ): TypeSkelet[T, Y, X] -⚬ ConcreteType[T] = {
        import ConcreteType.junctionConcreteType

        dsl.either(
          NonAbstractType.map(wrapX) > ConcreteType.nonAbstractType,
          λ { case lbl |*| req =>
            (lbl :>> labels.alsoDebugPrint(s => s"generifying abstract type $s")) match { case lbl =>
            RefinementRequest.decline(req) switch {
              case Left(x)   =>
                (lbl :>> labels.alsoDebugPrint(s => s"$s reinvigorated")) match { case lbl =>
                wrapX(x) waitFor labels.neglect(lbl)
                }
              case Right(nt) =>
                (lbl :>> labels.alsoDebugPrint(s => s"$s is asking for type arg")) match { case lbl =>
                ConcreteType.typeParam(labels.generify(lbl) |*| nt)
                }
            }
            }
          },
        )
      }

      def awaitPosFst[T, Y, X](
        g: (Done |*| X) -⚬ X,
      ): (Done |*| TypeSkelet[T, Y, X]) -⚬ TypeSkelet[T, Y, X] =
        λ { case d |*| t =>
          t switch {
            case Right(lbl |*| req) => injectR(lbl.waitFor(d) |*| req)
            case Left(t)            => (d |*| t) :>> NonAbstractType.awaitPosFst(g) :>> injectL
          }
        }
    }

    object TypeEmitterF {
      def pack[T, Y]: TypeSkelet[T, Y, TypeEmitterF[T, Y]] -⚬ TypeEmitterF[T, Y] =
        dsl.pack

      def unpack[T, Y]: TypeEmitterF[T, Y] -⚬ TypeSkelet[T, Y, TypeEmitterF[T, Y]] =
        dsl.unpack

      def contramap[T, Y, P](f: P -⚬ Y): TypeEmitterF[T, Y] -⚬ TypeEmitterF[T, P] =
        rec { self =>
          unpack[T, Y] > TypeSkelet.dimap(f, self) > pack[T, P]
        }
    }

    object TypeEmitter {

      private def pack0[T]: TypeEmitterF[T, ReboundTypeF[T, TypeEmitter[T]]] -⚬ TypeEmitter[T] =
        dsl.pack[[X] =>> TypeEmitterF[T, ReboundTypeF[T, X]]]

      private def unpack0[T]: TypeEmitter[T] -⚬ TypeEmitterF[T, ReboundTypeF[T, TypeEmitter[T]]] =
        dsl.unpack

      def pack1_[T](
        packRebound1: ReboundTypeF[T, TypeEmitter[T]] -⚬ ReboundType[T],
      ): TypeEmitterF[T, ReboundType[T]] -⚬ TypeEmitter[T] =
        TypeEmitterF.contramap(packRebound1) > pack0[T]

      private def pack1[T]: TypeEmitterF[T, ReboundType[T]] -⚬ TypeEmitter[T] =
        rec { self =>
          pack1_(ReboundType.pack1_(self))
        }

      def unpack1_[T](
        unpackRebound1: ReboundType[T] -⚬ ReboundTypeF[T, TypeEmitter[T]],
      ): TypeEmitter[T] -⚬ TypeEmitterF[T, ReboundType[T]] =
        unpack0[T] > TypeEmitterF.contramap(unpackRebound1)

      private def unpack1[T]: TypeEmitter[T] -⚬ TypeEmitterF[T, ReboundType[T]] =
        rec { self =>
          unpack1_(ReboundType.unpack1_(self))
        }

      def unpack[T]: TypeEmitter[T] -⚬ TypeSkelet[T, ReboundType[T], TypeEmitter[T]] =
        λ { t =>
          val t1: $[TypeEmitterF[T, ReboundType[T]]] = unpack1[T](t)
          val t2: $[TypeSkelet[T, ReboundType[T], TypeEmitterF[T, ReboundType[T]]]] = TypeEmitterF.unpack(t1)
          t2 :>> TypeSkelet.map(pack1)
        }

      def pack[T]: TypeSkelet[T, ReboundType[T], TypeEmitter[T]] -⚬ TypeEmitter[T] =
        λ { t =>
          val t1: $[TypeSkelet[T, ReboundType[T], TypeEmitterF[T, ReboundType[T]]]] = t :>> TypeSkelet.map(unpack1)
          val t2: $[TypeEmitterF[T, ReboundType[T]]] = TypeEmitterF.pack(t1)
          pack1(t2)
        }

      def unapply[T](using SourcePos)(a: $[TypeEmitter[T]])(using LambdaContext): Some[$[TypeSkelet[T, ReboundType[T], TypeEmitter[T]]]] =
        Some(unpack(a))

      def contramap_[T, U](f: T -⚬ U)(
        mapInbound: ReboundType[T] -⚬ ReboundType[U],
      ): TypeEmitter[U] -⚬ TypeEmitter[T] =
        rec { self =>
          unpack > dsl.either(
            NonAbstractType.map(self) > nonAbstractType[T],
            λ { case l |*| req =>
              val req1 = req
                :>> RefinementRequest.contramapT(f)
                :>> RefinementRequest.map(self)
                :>> RefinementRequest.contramap(mapInbound)
              abstractType(l |*| req1)
            },
          )
        }

      def contramap[T, U](f: T -⚬ U): TypeEmitter[U] -⚬ TypeEmitter[T] =
        rec { self =>
          contramap_(f)(ReboundType.map_(f)(self))
        }

      def nonAbstractType[T]: NonAbstractTypeF[TypeEmitter[T]] -⚬ TypeEmitter[T] =
        TypeSkelet.nonAbstractType > pack

      def abstractType[T]: (Label |*| RefinementRequest[T]) -⚬ TypeEmitter[T] =
        TypeSkelet.abstractType > pack

      def makeAbstractType[T]: Label -⚬ (TypeEmitter[T] |*| ReboundF[T, ReboundType[T], TypeEmitter[T]]) =
        TypeSkelet.makeAbstractType[T, ReboundType[T], TypeEmitter[T]] > fst(pack)

      def abstractTypeOut[T](
        outletT: (TParamLabel |*| T) -⚬ ConcreteType[Done],
      ): Label -⚬ (TypeEmitter[T] |*| ConcreteType[Done]) =
        λ { l =>
          val t |*| r = makeAbstractType[T](l)
          val o = r switch {
            case Left(r) =>
              r :>> ReboundType.outlet(outletT)
            case Right(value) =>
              value switch {
                case Left(req) =>
                  val --(t) = req :>> contrapositive(injectR)
                  outletT(labels.generify(l) |*| t)
                case Right(?(_)) =>
                  ???
              }
          }
          t |*| o
        }

      def abstractTypeTap[T](
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
      ): Label -⚬ (TypeEmitter[T] |*| Val[Type]) =
        λ { label =>
          val l1 |*| l2 = labels.split(label)
          val t |*| resp = TypeEmitter.makeAbstractType[T](l1)
          t |*| (resp switch {
            case Left(y) =>
              (y :>> ReboundType.output(outputT))
                .waitFor(labels.neglect(l2))
            case Right(value) =>
              value switch {
                case Left(req) =>
                  val --(t) = req contramap injectR
                  outputT(labels.generify(l2) |*| t)
                case Right(?(_)) =>
                  l2 :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
              }
          })
        }

      // def genericType[T](
      //   instantiate: ReboundType[T] -⚬ T,
      // ): (Val[AbstractTypeLabel] |*| -[T]) -⚬ TypeEmitter[T] =
      //   λ { case lbl |*| nt =>
      //     val out |*| resp = makeAbstractType[T](lbl)
      //     returning(
      //       out,
      //       resp switch {
      //         case Left(y) =>
      //           instantiate(y) supplyTo nt
      //         case Right(value) =>
      //           value switch {
      //             case Left(outReq) =>
      //               injectR(nt) supplyTo outReq
      //             case Right(?(_)) =>
      //               nt :>> crashNow(s"TODO: Is this case really ever used? (${summon[SourcePos]})")
      //           }
      //       }
      //     )
      //   }

      def newAbstractType[T](
        mergeT: (T |*| T) -⚬ T,
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
      )(using
        Junction.Positive[T],
      ): Label -⚬ (TypeEmitter[T] |*| Val[Type] |*| TypeEmitter[T]) =
        λ { label =>
          val a |*| t = label :>> abstractTypeTap(outputT)
          val x |*| y = a     :>> split(mergeT, outputT)
          x |*| t |*| y
        }
        // TypeSkelet.newAbstractType[T, ReboundType[T], TypeEmitter[T]](
        //   TypeEmitter.split(mergeT, outputT),
        //   ReboundType.merge(mergeT, outputT),
        //   ReboundType.tapFlop(mergeT, outputT),
        //   mergeT,
        //   ReboundType.output(outputT),
        //   outputT,
        // )
        //   > λ { case a |*| t |*| b => pack(a) |*| t |*| pack(b) }


      def pair[T]: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] =
        λ { case a |*| b => pack(TypeSkelet.nonAbstractType(NonAbstractType.pair(a |*| b))) }

      def either[T]: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T]=
        NonAbstractType.either > nonAbstractType

      // def isPair[T]: TypeEmitter[T] -⚬ (TypeEmitter[T] |+| (TypeEmitter[T] |*| TypeEmitter[T])) =
      //   unpack > dsl.either(
      //     NonAbstractType.isPair > |+|.lmap(nonAbstractType),
      //     abstractType > injectL,
      //   )

      def recCall[T]: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] =
        λ { case a |*| b => pack(TypeSkelet.nonAbstractType(NonAbstractType.recCall(a |*| b))) }

      // def isRecCall[T]: TypeEmitter[T] -⚬ (TypeEmitter[T] |+| (TypeEmitter[T] |*| TypeEmitter[T])) =
      //   unpack > dsl.either(
      //     NonAbstractType.isRecCall > |+|.lmap(nonAbstractType),
      //     abstractType > injectL,
      //   )

      def fixT[T, F[_]](F: TypeTag[F]): One -⚬ TypeEmitter[T] =
        NonAbstractType.fixT(F) > nonAbstractType

      def apply1T[T, F[_]](F: TypeTag[F]): TypeEmitter[T] -⚬ TypeEmitter[T] =
        apply1(TypeTag.toTypeFun(F))

      def apply1[T](f: TypeTagF): TypeEmitter[T] -⚬ TypeEmitter[T] = {
        // λ { t => NonAbstractType.apply1(constantVal(f) |*| t) :>> nonAbstractType }
        val ct = compilationTarget[T]
        import ct.Map_●
        f.compile[ct.Arr, ct.as, TypeEmitter[T]](Map_●)(ct.typeAlgebra, Map_●).get(Map_●, Map_●) > awaitPosFst
      }

      class compilationTarget[T] {
        type Arr[K, L] = K -⚬ (Done |*| L)

        val category: SymmetricMonoidalCategory[Arr, |*|, One] =
          new SymmetricMonoidalCategory[Arr, |*|, One] {

            override def id[A]: Arr[A, A] =
              dsl.introFst(done)

            override def introFst[A]: Arr[A, One |*| A] =
              dsl.andThen(dsl.introFst, dsl.introFst(done))

            override def introSnd[A]: Arr[A, A |*| One] =
              dsl.andThen(dsl.introSnd, dsl.introFst(done))

            override def elimFst[A]: Arr[One |*| A, A] =
              dsl.fst(done)

            override def elimSnd[A]: Arr[A |*| One, A] =
              dsl.andThen(dsl.swap, dsl.fst(done))

            override def assocRL[A, B, C]: Arr[A |*| (B |*| C), (A |*| B) |*| C] =
              dsl.andThen(dsl.assocRL, dsl.introFst(done))

            override def assocLR[A, B, C]: Arr[(A |*| B) |*| C, A |*| (B |*| C)] =
              dsl.andThen(dsl.assocLR, dsl.introFst(done))

            override def swap[A, B]: Arr[A |*| B, B |*| A] =
              dsl.andThen(dsl.swap, dsl.introFst(done))

            override def andThen[A, B, C](
              f: Arr[A, B],
              g: Arr[B, C],
            ): Arr[A, C] =
              dsl.andThen(
                dsl.andThen(f, dsl.snd(g)),
                dsl.andThen(dsl.assocRL, dsl.fst(join)),
              )

            override def par[A1, A2, B1, B2](
              f1: Arr[A1, B1],
              f2: Arr[A2, B2],
            ): Arr[A1 |*| A2, B1 |*| B2] =
              dsl.andThen(
                dsl.par(f1, f2),
                λ { case (d1 |*| b1) |*| (d2 |*| b2) =>
                  join(d1 |*| d2) |*| (b1 |*| b2)
                },
              )
          }

        val typeAlgebra: TypeAlgebra.Of[ScalaTypeParam, Arr, TypeEmitter[T], |*|, One] =
          new TypeAlgebra[ScalaTypeParam, Arr] {
            override type Type = TypeEmitter[T]
            override type <*>[A, B] = A |*| B
            override type None = One

            override def unit: Arr[One, TypeEmitter[T]] =
              done > λ { case +(d) => d |*| TypeEmitter.unit(d) }
            override def int: Arr[One, TypeEmitter[T]] =
              done > λ { case +(d) => d |*| TypeEmitter.int(d) }
            override def string: Arr[One, TypeEmitter[T]] =
              done > λ { case +(d) => d |*| TypeEmitter.string(d) }
            override def pair: Arr[TypeEmitter[T] |*| TypeEmitter[T], TypeEmitter[T]] =
              λ { case t |*| u => constant(done) |*| TypeEmitter.pair(t |*| u) }
            override def sum: Arr[TypeEmitter[T] |*| TypeEmitter[T], TypeEmitter[T]] =
              λ { case t |*| u => constant(done) |*| TypeEmitter.either(t |*| u) }
            override def recCall: Arr[TypeEmitter[T] |*| TypeEmitter[T], TypeEmitter[T]] =
              λ { case t |*| u => constant(done) |*| TypeEmitter.recCall(t |*| u) }
            override def fix(f: TypeFun[●, ●]): Arr[One, TypeEmitter[T]] =
              // const(f) > TypeEmitter.fix > introFst(done)
              ???
            override def abstractTypeName(name: ScalaTypeParam): Arr[One, TypeEmitter[T]] =
              throw NotImplementedError(s"TODO (${summon[SourcePos]})")

            override given category: SymmetricMonoidalCategory[Arr, |*|, One] =
              compilationTarget.this.category
          }

        sealed trait as[K, Q]

        case object Map_○ extends as[○, One]
        case object Map_● extends as[●, TypeEmitter[T]]
        case class Pair[K1, K2, Q1, Q2](
          f1: K1 as Q1,
          f2: K2 as Q2,
        ) extends as[K1 × K2, Q1 |*| Q2]

        given objectMap: MonoidalObjectMap[as, ×, ○, |*|, One] =
          new MonoidalObjectMap[as, ×, ○, |*|, One] {

            override def uniqueOutputType[A, B, C](f: as[A, B], g: as[A, C]): B =:= C =
              (f, g) match {
                case (Map_○, Map_○) => summon[B =:= C]
                case (Map_●, Map_●) => summon[B =:= C]
                case (Pair(f1, f2), Pair(g1, g2)) =>
                  (uniqueOutputType(f1, g1), uniqueOutputType(f2, g2)) match {
                    case (TypeEq(Refl()), TypeEq(Refl())) =>
                      summon[B =:= C]
                  }
              }

            override def pair[A1, A2, X1, X2](f1: as[A1, X1], f2: as[A2, X2]): as[A1 × A2, X1 |*| X2] =
              Pair(f1, f2)

            override def unpair[A1, A2, X](f: as[A1 × A2, X]): Unpaired[A1, A2, X] =
              f match {
                case Pair(f1, f2) => Unpaired.Impl(f1, f2)
              }

            override def unit: as[○, One] =
              Map_○
          }
      }

      def int[T]: Done -⚬ TypeEmitter[T] =
        NonAbstractType.int > nonAbstractType

      def string[T]: Done -⚬ TypeEmitter[T] =
        NonAbstractType.string > nonAbstractType

      def unit[T]: Done -⚬ TypeEmitter[T]=
        NonAbstractType.unit > nonAbstractType

      def split_[T](
        mergeInbound: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
        tapFlop: ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]),
        mergeT: (T |*| T) -⚬ T,
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) = rec { self =>
        unpack > TypeSkelet.split(self, mergeInbound, tapFlop, mergeT) > par(pack, pack)
      }

      def split[T](
        mergeT: (T |*| T) -⚬ T,
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
      )(using
        Junction.Positive[T],
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) = {
        val mergeInbound =
          ReboundType.merge_(
            mergeT,
            outputT,
          )

        split_(
          mergeInbound,
          ReboundType.tapFlop_(mergeInbound, mergeT),
          mergeT,
        )
      }

      def splitH__[T](
        splitTPreferred: T -⚬ (T |*| T),
        mergeInboundH: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T],
        splitInboundPreferred: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
        splitHPreferred1: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) =
        rec { self =>
          λ { case TypeEmitter(a) =>
            a :>> TypeSkelet.splitH(
              self,
              mergeInboundH,
              splitInboundPreferred,
              splitHPreferred1,
              splitTPreferred,
            ) > par(pack, ReboundType.pack)
          }
        }

      def splitH_[T](
        splitTPreferred: T -⚬ (T |*| T),
        mergeInboundH: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T],
        splitInboundPreferred: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) =
        rec { self =>
          splitH__(
            splitTPreferred,
            mergeInboundH,
            splitInboundPreferred,
            splitHPreferred1__(splitTPreferred, splitInboundPreferred, self),
          )
        }

      def splitH[T](
        splitTPreferred: T -⚬ (T |*| T),
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) =
        rec { self =>
          val (splitHPreferred1, splitInboundPreferred) = rec2 { (
            splitHPreferred1: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
            splitInboundPreferred: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
          ) =>
            ( splitHPreferred1__(splitTPreferred, splitInboundPreferred, self)
            , ReboundType.splitPreferred_(splitTPreferred, self, splitHPreferred1)
            )
          }
          splitH_(
            splitTPreferred,
            ReboundType.mergeH_(
              self,
              splitHPreferred1,
              splitTPreferred,
              outputT,
              outputTParam,
            ),
            splitInboundPreferred,
          )
        }

      def splitHPreferred1__[T](
        splitTPreferred: T -⚬ (T |*| T),
        splitInboundPreferred: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
        splitH: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) =
        rec { self =>
          λ { case TypeEmitter(a) =>
            a :>> TypeSkelet.splitHPreferred1(
              splitH,
              self,
              splitInboundPreferred,
              pack,
              ReboundType.pack,
              splitTPreferred,
            )
          }
        }

      def splitHPreferred1_[T](
        splitTPreferred: T -⚬ (T |*| T),
        mergeInboundH: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T],
        splitInboundPreferred: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) =
        rec { self =>
          splitHPreferred1__(
            splitTPreferred,
            splitInboundPreferred,
            splitH__(
              splitTPreferred,
              mergeInboundH,
              splitInboundPreferred,
              self,
            ),
          )
        }

      def splitHPreferred1[T](
        splitTPreferred: T -⚬ (T |*| T),
        outputT: (TParamLabel |*| T) -⚬ Val[Type],
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) = rec { self =>
        val (mergeInboundH, splitInboundPreferred) = rec2 { (
          mergeInboundH: (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T],
          splitInboundPreferred: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
        ) => (
          ReboundType.mergeH_(
            splitH__(splitTPreferred, mergeInboundH, splitInboundPreferred, self),
            self,
            splitTPreferred,
            outputT,
            outputTParam,
          ),
          ReboundType.splitPreferred_(
            splitTPreferred,
            splitH__(splitTPreferred, mergeInboundH, splitInboundPreferred, self),
            self,
          ),
        ) }

        splitHPreferred1_(
          splitTPreferred,
          mergeInboundH,
          splitInboundPreferred,
        )
      }

      def tapFlip__[T](
        splitT: T -⚬ (T |*| T),
        splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) =
        rec { self =>
          λ { case TypeEmitter(a) =>
            a :>> TypeSkelet.tapFlip(
              splitRebound,
              self,
              TypeEmitter.pack,
              ReboundType.pack,
              splitT,
            )
          }
        }

      def tapFlip_[T](
        splitT: T -⚬ (T |*| T),
        splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) =
        tapFlip__(splitT, splitRebound)

      def tapFlip[T](
        splitT: T -⚬ (T |*| T),
        neglectT: T -⚬ Done,
        outputTParamApprox: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) = rec { self =>
        val splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) =
          rec { splitRebound =>
            ReboundType.split_(
              splitT,
              merge__(
                splitT,
                outputTParamApprox,
                splitRebound,
                self,
              ),
              self,
            )
          }

        tapFlip_(
          splitT,
          splitRebound,
        )
      }

      def merge__[T](
        splitT: T -⚬ (T |*| T),
        outputTParamApprox: (TParamLabel |*| -[T]) -⚬ Val[Type],
        splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
        tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
      ): (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] = rec { self =>
        λ { case TypeEmitter(a) |*| TypeEmitter(b) =>
          TypeSkelet.merge(
            self,
            splitY = splitRebound,
            tapFlipXY = tapFlip,
            makeX = pack,
            makeY = ReboundType.pack,
            splitT = splitT,
            outputApprox(outputTParamApprox),
          )(a |*| b)
        }
      }

      def merge_[T](
        splitT: T -⚬ (T |*| T),
        outputTParamApprox: (TParamLabel |*| -[T]) -⚬ Val[Type],
        splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      ): (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] = rec { self =>
        merge__(
          splitT,
          outputTParamApprox,
          splitRebound,
          tapFlip__(splitT, splitRebound),
        )
      }

      def merge[T](
        splitT: T -⚬ (T |*| T),
        outputTParamApprox: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] = rec { self =>
        val splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]) =
          rec { splitRebound =>
            val tapFlip =
              tapFlip__(
                splitT,
                splitRebound,
              )
            ReboundType.split_(splitT, self, tapFlip)
          }

        merge_(
          splitT,
          outputTParamApprox,
          splitRebound,
        )
      }

      // def mergeIn__[T](
      //   split: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
      //   mergeRebound: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      //   tapFlop: ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]),
      //   mergeT: (T |*| T) -⚬ T,
      //   neglectT: T -⚬ Done,
      //   outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      // ): (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] = rec { self =>
      //   λ { case a |*| b =>
      //     val a1: $[TypeSkelet[  T , ReboundType[T], TypeEmitter[T]]] = unpack(a)
      //     val b1: $[TypeSkelet[-[T], TypeEmitter[T], ReboundType[T]]] = ReboundType.unpack(b)

      //     (a1 |*| b1) :>> TypeSkelet.mergeOpWith[T, -[T], ReboundType[T], TypeEmitter[T]](
      //       split,
      //       self,
      //       tapFlop,
      //       mergeT,
      //       TypeEmitter.pack,
      //       ReboundType.pack,
      //       λ { t =>
      //         producing { case ot |*| ont =>
      //           ot := mergeT(t |*| ont.asInput)
      //         }
      //       },
      //       λ { case nt |*| t =>
      //         val nt1 |*| nt2 = distributeInversion(nt contramap mergeT)
      //         returning(
      //           nt1,
      //           t supplyTo nt2,
      //         )
      //       },
      //       TypeEmitter.outputApprox(outputTParam),
      //       ReboundType.outputApprox(neglectT),
      //     )
      //   }
      // }

      // def mergeIn_[T](
      //   mergeInbound: (ReboundType[T] |*| ReboundType[T]) -⚬ ReboundType[T],
      //   tapFlop: ReboundType[T] -⚬ (ReboundType[T] |*| TypeEmitter[T]),
      //   mergeT: (T |*| T) -⚬ T,
      //   neglectT: T -⚬ Done,
      //   outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      // ): (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] =
      //   mergeIn__[T](
      //     split_(mergeInbound, tapFlop, mergeT),
      //     mergeInbound,
      //     tapFlop,
      //     mergeT,
      //     neglectT,
      //     outputTParam,
      //   )

      // def mergeIn[T](
      //   mergeT: (T |*| T) -⚬ T,
      //   neglectT: T -⚬ Done,
      //   outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      //   outputT: (Label |*| T) -⚬ Val[Type],
      // )(using
      //   Junction.Positive[T],
      // ): (TypeEmitter[T] |*| ReboundType[T]) -⚬ TypeEmitter[T] = {
      //   val mergeInbound =
      //     ReboundType.merge_(
      //       mergeT,
      //       neglectT,
      //       outputT,
      //     )

      //   mergeIn_[T](
      //     mergeInbound,
      //     ReboundType.tapFlop_(mergeInbound, mergeT),
      //     mergeT,
      //     neglectT,
      //     outputTParam,
      //   )
      // }

      // def mergeFlip[T](
      //   merge: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
      //   split: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]),
      //   flipSplit: TypeEmitter[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
      //   newAbstractLink: One -⚬ (TypeEmitter[T] |*| ReboundType[T]),
      //   instantiate: TypeEmitter[T] -⚬ T,
      // ): (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] = rec { self =>
      //   λ { case a |*| b =>
      //     val a1: $[TypeSkelet[T, ReboundType[T], TypeEmitter[T]]] = unpack(a)
      //     val b1: $[TypeSkelet[T, ReboundType[T], TypeEmitter[T]]] = unpack(b)
      //     val c: $[TypeSkelet[-[T], TypeEmitter[T], ReboundType[T]]] =
      //       (a1 |*| b1) :>> TypeSkelet.mergeFlip(merge, split, flipSplit, self, newAbstractLink, instantiate, ReboundType.pack)
      //     ReboundType.pack(c)
      //   }
      // }

      def outputApprox[T](
        outputTParamApprox: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): TypeEmitter[T] -⚬ Val[Type] =
        rec { self =>
          unpack > TypeSkelet.outputApprox(self, outputTParamApprox)
        }

      def output[T](
        outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
      ): TypeEmitter[T] -⚬ Val[Type] =
        rec { self =>
          unpack > TypeSkelet.output(self, outputTParam)
        }

      def outlet[T](
        outletTParam: (TParamLabel |*| -[T]) -⚬ ConcreteType[Done],
        // outletTParam: (TParamLabel |*| -[T]) -⚬ TypeOutlet[Done],
      ): TypeEmitter[T] -⚬ ConcreteType[Done] =
        rec { self =>
          unpack > TypeSkelet.outlet(self, outletTParam)
        }

      def probeApprox[T](
        outputTypeArg: (TParamLabel |*| T) -⚬ Val[Type],
      ): (TParamLabel |*| -[TypeEmitter[T]]) -⚬ Val[Type] =
        λ { case label |*| nt =>
          val lbl1 |*| lbl2 = labels.split(labels.abstractify(label))
          val t |*| reb = makeAbstractType[T](lbl1)
          returning(
            reb switch {
              case Left(x) =>
                ReboundType.outputApprox(outputTypeArg)(x)
                  .waitFor(labels.neglect(lbl2))
              case Right(value) =>
                value switch {
                  case Left(req) =>
                    val --(t) = req contramap injectR
                    val l = labels.generify(lbl2)
                    outputTypeArg(l |*| t)
                  case Right(?(_)) =>
                    lbl2 :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
                }
            },
            t supplyTo nt,
          )
        }

      def probe[T](
        // outletTypeArg: (TParamLabel |*| T) -⚬ TypeOutlet[Done],
        outletTypeArg: (TParamLabel |*| T) -⚬ ConcreteType[Done],
      ): (TParamLabel |*| -[TypeEmitter[T]]) -⚬ ConcreteType[Done] =
        λ { case label |*| nt =>
          val lbl1 |*| lbl2 = labels.split(labels.abstractify(label))
          val t |*| reb = makeAbstractType[T](lbl1)
          returning(
            reb switch {
              case Left(x) =>
                import ReboundType.junctionReboundType
                x.waitFor(labels.neglect(lbl2))
                  :>> ReboundType.outlet(outletTypeArg)
              case Right(value) =>
                value switch {
                  case Left(req) =>
                    val --(t) = req contramap injectR
                    val l = labels.generify(lbl2)
                    outletTypeArg(l |*| t)
                  case Right(?(_)) =>
                    lbl2 :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
                }
            },
            t supplyTo nt,
          )
        }

      def close[T](
        closeTParam: (TParamLabel |*| -[T]) -⚬ Done,
      ): TypeEmitter[T] -⚬ Done =
        rec { self =>
          unpack > TypeSkelet.close(self, closeTParam)
        }

      def generify[T]: TypeEmitter[T] -⚬ ConcreteType[T] =
        rec { self =>
          unpack > TypeSkelet.generify(self)
        }

      // def disengage[T]: TypeEmitter[T] -⚬ Done = rec { self =>
      //   λ { case TypeEmitter(t) =>
      //     t switch {
      //       case Right(lbl |*| req) =>
      //         returning(
      //           neglect(lbl),
      //           RefinementRequest.decline0(req),
      //         )
      //       case Left(t) => t switch {
      //         case Right(a |*| b) => join(self(a) |*| self(b))
      //         case Left(t) => t switch {
      //           case Right(a |*| b) => join(self(a) |*| self(b))
      //           case Left(t) => t switch {
      //             case Right(a |*| b) => join(self(a) |*| self(b))
      //             case Left(t) => t switch {
      //               case Right(f) => neglect(f)
      //               case Left(t) => t switch {
      //                 case Right(f |*| x) => join(neglect(f) |*| self(x))
      //                 case Left(t) => t switch {
      //                   case Right(t) => t
      //                   case Left(t) => t switch {
      //                     case Right(t) => t
      //                     case Left(t) => t switch {
      //                       case Right(t) => t
      //                       case Left(t) => neglect(t)
      //                     }
      //                   }
      //                 }
      //               }
      //             }
      //           }
      //         }
      //       }
      //     }
      //   }
      // }

      def awaitPosFst[T]: (Done |*| TypeEmitter[T]) -⚬ TypeEmitter[T] =
        rec { self =>
          λ { case d |*| t =>
            (d |*| unpack(t)) :>> TypeSkelet.awaitPosFst(self) :>> pack
          }
        }

      given junctionTypeEmitter[T]: Junction.Positive[TypeEmitter[T]] with {
        override def awaitPosFst: (Done |*| TypeEmitter[T]) -⚬ TypeEmitter[T] =
          TypeEmitter.awaitPosFst
      }
    }

    type GenericType[T] = ConcreteType[T]

    val tParamToType: TParamLabel -⚬ Val[Type] =
      labels.unwrapOriginalTP > mapVal(x => Type.abstractType(x))

    val outputTParam: (TParamLabel |*| -[Done]) -⚬ Val[Type] =
      λ { case lbl |*| nd =>
        val (res |*| d) = tParamToType(lbl) :>> signalPosSnd
        returning(
          res,
          d supplyTo nd,
        )
      }

    val closeTParam: (TParamLabel |*| -[Done]) -⚬ Done =
      λ { case lbl |*| nd =>
        val d1 |*| d2 = labels.neglectTParam(lbl) > fork
        returning(
          d1,
          d2 supplyTo nd,
        )
      }

    val groundInstance: ToolsImpl[Done] =
      ToolsImpl(
        join,
        fork,
        fst(tParamToType) > awaitPosSnd,
        outputTParam,
        id[Done],
        closeTParam,
      )
  }

  private[typeinfer] class ToolsImpl[T](
    mergeT: (T |*| T) -⚬ T,
    splitT: T -⚬ (T |*| T),
    outputT: (TParamLabel |*| T) -⚬ Val[ToolsImpl.Type],
    outputTParam: (TParamLabel |*| -[T]) -⚬ Val[ToolsImpl.Type],
    neglectT: T -⚬ Done,
    neglectTParam: (TParamLabel |*| -[T]) -⚬ Done,
  )(using
    T: Junction.Positive[T],
  ) extends Tools { self =>
    import ToolsImpl.*

    override type Label = labels.Label
    override type OutboundType = TypeEmitter[T]
    override type SplittableType = TypeEmitter[T]
    override type MergeableType = TypeEmitter[T]
    // override type InboundType = ReboundType[T]
    override type OutwardType = ConcreteType[T]

    override lazy val nested: Nested =
      new Nested {

        override val tools: ToolsImpl[ReboundType[T]] =
          import ReboundType.junctionReboundType
          ToolsImpl[ReboundType[T]](
            ReboundType.merge(mergeT, outputT),
            ReboundType.split(splitT, outputTParam),
            fst(labels.neglectTParam) > ReboundType.awaitPosFst > ReboundType.output(outputT),
            ReboundType.probeApprox(outputTParam),
            ReboundType.close(neglectT),
            ReboundType.probeApprox(outputTParam) > neglect,
          )

        override lazy val mergeLower: (tools.OutwardType |*| tools.OutwardType) -⚬ self.OutboundType =
          ConcreteType.mergeLower(splitT, outputTParam)

        override lazy val mergeZap: (tools.OutwardType |*| tools.OutwardType) -⚬ Val[Type] =
          ConcreteType.mergeZap0(splitT, outputTParam)

        override lazy val unnest: tools.OutboundType -⚬ self.OutboundType =
          TypeEmitter.generify > ConcreteType.abstractify[T]

        override def unnestM: tools.MergeableType -⚬ self.OutboundType =
          unnest

        override def unnestS: tools.SplittableType -⚬ self.OutboundType =
          unnest

        override lazy val unnestOutward: tools.OutwardType -⚬ self.OutwardType =
          ConcreteType.abstractify[T] > TypeEmitter.generify

        override def lower: tools.OutwardType -⚬ OutboundType = UnhandledCase.raise("")
      }

    override lazy val abstractTypeTap: Label -⚬ (TypeEmitter[T] |*| Val[Type]) =
      TypeEmitter.abstractTypeTap(outputT)

    override def abstractLink: Label -⚬ (OutboundType |*| OutboundType) = ???

    // override lazy val newAbstractType: Label -⚬ (TypeEmitter[T] |*| Val[Type] |*| TypeEmitter[T]) =
    //   TypeEmitter.newAbstractType(mergeT, outputT)

    // def newAbstractTypeGen: Label -⚬ (GenericType[T] |*| Val[Type] |*| GenericType[T]) =
    //   newAbstractType > λ { case a |*| t |*| b =>
    //     TypeEmitter.generify(a) |*| t |*| TypeEmitter.generify(b)
    //   }

    // override lazy val newTypeParam: Label -⚬ (Val[Type] |*| OutboundType) =
    //   λ { label =>
    //     val l1 |*| l2 = labels.split(label)
    //     val nt |*| t = constant(demand[T])
    //     outputT(labels.generify(l1) |*| t) |*| TypeEmitter.typeParam(labels.generify(l2) |*| nt)
    //   }

    override def mergeable: OutboundType -⚬ MergeableType =
      id

    override def splittable: OutboundType -⚬ SplittableType =
      id

    override lazy val merge: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] =
      TypeEmitter.merge(splitT, outputTParam)

    // override lazy val mergeZap: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ Val[Type] =
    //   TypeEmitter.merge(splitT, outputTParam) > output

    // override lazy val mergeGenTap: (GenericType[ReboundType[T]] |*| GenericType[ReboundType[T]]) -⚬ (GenericType[T] |*| ConcreteType[Done]) =
    //   ConcreteType.mergeTap(splitT, splitTPreferred, outletT, outputT, outputTParam) > fst(TypeEmitter.generify)

    // override lazy val mergeGenTap: (GenericType[ReboundType[T]] |*| GenericType[ReboundType[T]]) -⚬ (GenericType[T] |*| Val[Type]) =
    //   ???

    // override lazy val mergeGen2: (GenericType[TypeEmitter[T]] |*| GenericType[TypeEmitter[T]]) -⚬ GenericType[T] =
    //   ConcreteType.merge2(split, outputTParam)

    override lazy val split: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      TypeEmitter.split(mergeT, outputT)

    // override lazy val outlet: TypeEmitter[T] -⚬ ConcreteType[Done] =
    //   TypeEmitter.outlet(outletTParam)

    override lazy val tap: OutboundType -⚬ OutwardType =
      TypeEmitter.generify

    override def tapM: MergeableType -⚬ OutwardType =
      tap

    override def tapS: SplittableType -⚬ OutwardType =
      tap

    override lazy val outputOW: GenericType[T] -⚬ Val[Type] =
      ConcreteType.output(outputTParam)

    override lazy val output: TypeEmitter[T] -⚬ Val[Type] =
      TypeEmitter.generify > outputOW

    override lazy val closeOW: GenericType[T] -⚬ Done =
      ConcreteType.close[T](outputTParam > dsl.neglect)

    override lazy val close: TypeEmitter[T] -⚬ Done =
      TypeEmitter.generify[T] > closeOW

    override lazy val debugPrintGradually: TypeEmitter[T] -⚬ Done =
      TypeEmitter.generify > ConcreteType.debugPrintGradually(outputTParam > printLine(_.toString))

    override def label(v: AbstractTypeLabel): One -⚬ Label =
      labels.create(Right(v))

    override lazy val pair: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] =
      TypeEmitter.pair

    override lazy val pairOW: (OutwardType |*| OutwardType) -⚬ OutwardType =
      ConcreteType.recCall[T]

    // override lazy val isPair: TypeEmitter[T] -⚬ (TypeEmitter[T] |+| (TypeEmitter[T] |*| TypeEmitter[T])) =
    //   TypeEmitter.isPair

    override lazy val isPair: OutwardType -⚬ (OutwardType |+| (OutwardType |*| OutwardType)) =
      ConcreteType.isPair[T]

    override lazy val either: (OutboundType |*| OutboundType) -⚬ OutboundType =
      TypeEmitter.either[T]

    override lazy val eitherOW: (GenericType[T] |*| GenericType[T]) -⚬ GenericType[T] =
      ConcreteType.either[T]

    override lazy val recCall: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T] =
      TypeEmitter.recCall

    override lazy val recCallOW: (OutwardType |*| OutwardType) -⚬ OutwardType =
      ConcreteType.recCall[T]

    // override lazy val isRecCall: TypeEmitter[T] -⚬ (TypeEmitter[T] |+| (TypeEmitter[T] |*| TypeEmitter[T])) =
    //   TypeEmitter.isRecCall

    override lazy val isRecCall: OutwardType -⚬ (OutwardType |+| (OutwardType |*| OutwardType)) =
      ConcreteType.isRecCall[T]

    override def fixT[F[_]](F: TypeTag[F]): One -⚬ OutboundType =
      TypeEmitter.fixT(F)

    override def fixTOW[F[_]](F: TypeTag[F]): One -⚬ OutwardType =
      ConcreteType.fixT(F)

    override def apply1T[F[_]](F: TypeTag[F]): OutboundType -⚬ OutboundType =
      TypeEmitter.apply1T(F)

    override def apply1TOW[F[_]](F: TypeTag[F]): GenericType[T] -⚬ GenericType[T] =
      ConcreteType.apply1T(F)

    override lazy val int: Done -⚬ OutboundType =
      TypeEmitter.int[T]

    override lazy val intOW: Done -⚬ OutwardType =
      ConcreteType.int[T]

    override lazy val string: Done -⚬ OutboundType =
      TypeEmitter.string[T]

    override lazy val stringOW: Done -⚬ OutwardType =
      ConcreteType.string[T]
  }

  val instance: Tools =
    ToolsImpl.groundInstance
}
