package libretto.typology.toylang.typeinfer

import java.util.concurrent.atomic.AtomicInteger
import libretto.lambda.{MonoidalObjectMap, SymmetricMonoidalCategory}
import libretto.lambda.util.{Monad, SourcePos, TypeEq}
import libretto.lambda.util.Monad.syntax._
import libretto.lambda.util.TypeEq.Refl
import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.Comonoid.comonoidOne
import libretto.typology.kinds.{×, ○, ●}
import libretto.typology.toylang.terms.{Fun, FunT, TypedFun}
import libretto.typology.toylang.types.{Fix, AbstractTypeLabel, ScalaTypeParam, TypeAlgebra, TypeFun, TypeTag}
import libretto.typology.util.State

object TypeInference {
  object Labels {
    enum Lbl:
      case Base(value: AbstractTypeLabel, counter: AtomicInteger)
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

      def originalBase: AbstractTypeLabel =
        this match
          case Base(value, _) => value
          case Clone(base, tag) => base.originalBase
          case Abstracted(TParamLbl.Promoted(base), _) => base.originalBase

      override def toString =
        this match
          case Abstracted(base, _) => s"$base+"
          case Base(value, _) => s"{${value.value}}"
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
            (x.value compareTo y.value) match {
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

    def make(v: AbstractTypeLabel)(using SourcePos, LambdaContext): $[Label] =
      constantVal(Lbl.Base(v, AtomicInteger(0))) > alsoPrintLine(x => s"Creating $x")

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

    // val promote: Label -⚬ Label =
    //   mapVal { Lbl.Promoted(_) }

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

    val toAbstractType: TParamLabel -⚬ Val[Type] =
      mapVal { case x @ TParamLbl.Promoted(l) =>
        val res: Type = Type.abstractType(Right(l.originalBase))
        println(s"$x outputted as $res")
        res
      }

    val show: Label -⚬ Val[String] =
      // mapVal(_.toString)
      mapVal(x =>
        val res = x.toString
        println(s"$x converted to string")
        res
      )

    given Junction.Positive[Label] =
      scalettoLib.junctionVal

    given Junction.Positive[TParamLabel] =
      scalettoLib.junctionVal
  }

  import Labels.{Label, TParamLabel}

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

  type TypeFun[K, L] = libretto.typology.toylang.types.TypeFun[AbstractTypeLabel, K, L]
  // def  TypeFun = libretto.typology.toylang.types.TypeFun

  type TypeTagF = libretto.typology.toylang.types.TypeFun[ScalaTypeParam, ●, ●]

  private type NonAbstractTypeF[X] = (
    Val[(Type, Type)] // type mismatch
    |+| Done // unit
    |+| Done // int
    |+| Done // string
    |+| (Val[TypeTagF] |*| X) // apply1 // TODO: eliminate?
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

  object RefinementRequest {
    def map[T, Y, X, Q](g: X -⚬ Q): RefinementRequestF[T, Y, X] -⚬ RefinementRequestF[T, Y, Q] =
      contrapositive(Rebound.contramap(g))

    def contramap[T, Y, X, P](f: P -⚬ Y): RefinementRequestF[T, Y, X] -⚬ RefinementRequestF[T, P, X] =
      contrapositive(Rebound.map(f))

    def completeWith[T, Y, X]: (RefinementRequestF[T, Y, X] |*| Y) -⚬ One =
      λ { case req |*| y => injectL(y) supplyTo req }

    def decline[T, Y, X]: RefinementRequestF[T, Y, X] -⚬ (X |+| -[T]) =
      λ { req =>
        req
          .contramap(injectR ∘ injectL)
          .unInvertWith(forevert > swap)
      }

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
  }

  object Rebound {
    def map[T, Y, X, Q](f: Y -⚬ Q): ReboundF[T, Y, X] -⚬ ReboundF[T, Q, X] =
      |+|.lmap(f)

    def contramap[T, Y, X, P](g: P -⚬ X): ReboundF[T, Y, X] -⚬ ReboundF[T, Y, P] =
      |+|.rmap(Yield.contramap(g))

    def unrefined[T, Y, X]: -[X |+| -[T]] -⚬ ReboundF[T, Y, X] =
      injectR ∘ injectL

    def makeUnrefined[T, Y, X]: One -⚬ (ReboundF[T, Y, X] |*| (X |+| -[T])) =
      demand[X |+| -[T]] > fst(unrefined)

    // def dup[T, X, Y](
    //   splitY: Y -⚬ (Y |*| Y),
    // ): ReboundF[T, Y, X] -⚬ (ReboundF[T, Y, X] |*| ReboundF[T, Y, X]) =
    //   either(
    //     splitY > par(injectL, injectL),
    //     either(
    //       λ { yld => injectR(injectL(yld)) |*| injectR(injectR($.one)) }, // XXX: arbitrarily propagating to one side
    //       λ { case +(one) => injectR(injectR(one)) |*| injectR(injectR(one)) },
    //     )
    //   )

    def flopSplit[T, Y, X](
      mergeX: (X |*| X) -⚬ X,
      splitX: X -⚬ (X |*| X),
      flipSplitX: X -⚬ (Y |*| Y),
      mergeFlipX: (X |*| X) -⚬ Y,
      newAbstractLink: One -⚬ (X |*| Y),
      instantiate: X -⚬ T,
    ): ReboundF[-[T], X, Y] -⚬ (ReboundF[T, Y, X] |*| ReboundF[T, Y, X]) =
      either(
        flipSplitX > par(injectL, injectL),
        Yield.flopSplit(mergeX, splitX, mergeFlipX, newAbstractLink, instantiate) > par(injectR, injectR),
      )

    def tapFlipWith[P, Q, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      tapFlopYX: Y -⚬ (Y |*| X),
      makeP: Y -⚬ P,
      makeQ: X -⚬ Q,
      tapFlipPQ: P -⚬ (P |*| Q),
    ): ReboundF[P, Y, X] -⚬ (ReboundF[P, Y, X] |*| ReboundF[Q, X, Y]) =
      either(
        tapFlopYX > par(injectL, injectL),
        Yield.tapFlipWith(splitX, mergeInXY, tapFlopYX, makeP, makeQ, tapFlipPQ) > par(injectR, injectR),
      )

    def tapFlip[T, Y, X](
      tapFlopY: Y -⚬ (Y |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      mergeInXT: (X |*| T) -⚬ X,
      yt: Y -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): ReboundF[T, Y, X] -⚬ (ReboundF[T, Y, X] |*| ReboundF[-[T], X, Y]) =
      either(
        tapFlopY > par(injectL, injectL),
        Yield.tapFlip(mergeInXY, mergeInXT, yt, mergeT) > par(injectR, injectR),
      )

    // def mergeFlip[T, Y, X](
    //   splitX: X -⚬ (X |*| X),
    //   mergeInXY: (X |*| Y) -⚬ X,
    //   tapFlop: Y -⚬ (Y |*| X),
    //   mergeT: (T |*| T) -⚬ T,
    // ): (ReboundF[-[T], X, Y] |*| ReboundF[T, Y, X]) -⚬ ReboundF[-[T], X, Y] =
    //   λ { case a |*| b =>
    //     a switch {
    //       case Left(refinedA) =>
    //         b switch {
    //           case Left(refinedB) =>
    //             injectL(mergeInXY(refinedA |*| refinedB))
    //           case Right(yieldB) =>
    //             yieldB switch {
    //               case Left(yieldB) =>
    //                 val x1 |*| x2 = splitX(refinedA)
    //                 returning(
    //                   injectL(x1),
    //                   injectL(x2) supplyTo yieldB,
    //                 )
    //               case Right(?(_)) =>
    //                 injectL(refinedA)
    //             }
    //         }
    //       case Right(yieldA) =>
    //         b switch {
    //           case Left(refinedB) =>
    //             yieldA switch {
    //               case Left(yieldA) =>
    //                 val y |*| x = tapFlop(refinedB)
    //                 returning(
    //                   injectL(x),
    //                   injectL(y) supplyTo yieldA,
    //                 )
    //               case Right(?(_)) =>
    //                 refinedB :>> crashNow(s"TODO: eliminate this path (${summon[SourcePos]})")
    //                 // injectL(refinedB)
    //             }
    //           case Right(yieldB) =>
    //             injectR((yieldA |*| yieldB) :>> Yield.mergeFlip(tapFlop, mergeT))
    //         }
    //     }
    //   }

    def mergeIn[T, Y, X](
      splitY: Y -⚬ (Y |*| Y),
      mergeInYX: (Y |*| X) -⚬ Y,
      tapFlip: X -⚬ (X |*| Y),
      splitT: T -⚬ (T |*| T),
    ): (ReboundF[T, Y, X] |*| ReboundF[-[T], X, Y]) -⚬ ReboundF[T, Y, X] =
      λ { case a |*| b =>
        a switch {
          case Left(refinedA) =>
            b switch {
              case Left(refinedB) =>
                injectL(mergeInYX(refinedA |*| refinedB))
              case Right(yieldB) =>
                yieldB switch {
                  case Left(yieldB) =>
                    val y1 |*| y2 = splitY(refinedA)
                    returning(
                      injectL(y1),
                      injectL(y2) supplyTo yieldB,
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
                    val x |*| y = tapFlip(refinedB)
                    returning(
                      injectL(y),
                      injectL(x) supplyTo yieldA,
                    )
                  case Right(?(_)) =>
                    ???
                    // injectL(refinedB)
                }
              case Right(yieldB) =>
                injectR((yieldA |*| yieldB) :>> Yield.mergeIn(tapFlip, splitT))
            }
        }
      }

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

    def flopSplit[T, Y, X](
      mergeX: (X |*| X) -⚬ X,
      splitX: X -⚬ (X |*| X),
      mergeFlipX: (X |*| X) -⚬ Y,
      newAbstractLink: One -⚬ (X |*| Y),
      instantiate: X -⚬ T,
    ): YieldF[-[T], Y] -⚬ (YieldF[T, X] |*| YieldF[T, X]) =
      val splitLink: X -⚬ (X |*| Y) =
        ???
      λ { _ switch {
        case Left(-(out)) =>
          producing { case in1 |*| in2 =>
            val x1 = (injectL >>: in1).asInput
            val x2 = (injectL >>: in2).asInput

            out :=
              x1 switch {
                case Left(x1) =>
                  x2 switch {
                    case Left(x2) =>
                      injectL(mergeFlipX(x1 |*| x2))
                    case Right(u) =>
                      val x |*| y = constant(newAbstractLink)
                      returning(
                        injectL(y),
                        instantiate(mergeX(x |*| x1)) supplyTo u,
                      )
                  }
                case Right(t) =>
                  x2 switch {
                    case Left(x2) =>
                      val x |*| y = constant(newAbstractLink)
                      returning(
                        injectL(y),
                        instantiate(mergeX(x |*| x2)) supplyTo t,
                      )
                    case Right(u) =>
                      val x |*| y = constant(newAbstractLink)
                      val x1 |*| x2 = splitX(x)
                      returning(
                        injectL(y),
                        instantiate(x1) supplyTo(t),
                        instantiate(x2) supplyTo(u),
                      )
                  }
              }
          }
        case Right(?(_)) =>
          ???
      }}

    def tapFlipWith[P, Q, Y, X](
      splitX: X -⚬ (X |*| X),
      mergeInXY: (X |*| Y) -⚬ X,
      tapFlopYX: Y -⚬ (Y |*| X),
      makeP: Y -⚬ P,
      makeQ: X -⚬ Q,
      tapFlipPQ: P -⚬ (P |*| Q),
    ): YieldF[P, X] -⚬ (YieldF[P, X] |*| YieldF[Q, Y]) =
      // val aux: (T |*| -[T]) -⚬ -[T] =
      //   λ { case t |*| nt =>
      //     val nt1 |*| t1 = constant(forevert[T])
      //     returning(nt1, mergeT(t |*| t1) supplyTo nt)
      //   }

      λ { _ switch {
        case Left(-(out)) =>
          producing { case in1 |*| in2 =>
            val x = (injectL >>: in1).asInput
            val y = (injectL >>: in2).asInput

            out :=
              x switch {
                case Left(x) =>
                  y switch {
                    case Left(y) =>
                      injectL(mergeInXY(x |*| y))
                    case Right(nq) =>
                      val x1 |*| x2 = splitX(x)
                      returning(
                        injectL(x1),
                        makeQ(x2) supplyTo nq,
                      )
                  }
                case Right(np) =>
                  y switch {
                    case Left(y) =>
                      val y1 |*| x = tapFlopYX(y)
                      returning(
                        injectL(x),
                        makeP(y1) supplyTo np,
                      )
                    case Right(nq) =>
                      producing { out =>
                        val out1 = factorOutInversion >>: contrapositive(tapFlipPQ) >>: injectR >>: out
                        out1 := (np |*| nq)
                      }
                  }
              }
          }
        case Right(one) =>
          one :>> crashNow(s"TODO: eliminate this path ${summon[SourcePos]}")
      }}

    def tapFlip[T, Y, X](
      mergeInXY: (X |*| Y) -⚬ X,
      mergeInXT: (X |*| T) -⚬ X,
      yt: Y -⚬ T,
      mergeT: (T |*| T) -⚬ T,
    ): YieldF[T, X] -⚬ (YieldF[T, X] |*| YieldF[-[T], Y]) =
      val aux: (T |*| -[T]) -⚬ -[T] =
        λ { case t |*| nt =>
          val nt1 |*| t1 = constant(forevert[T])
          returning(nt1, mergeT(t |*| t1) supplyTo nt)
        }

      λ { _ switch {
        case Left(-(out)) =>
          producing { case in1 |*| in2 =>
            val x = (injectL >>: in1).asInput
            val y = (injectL >>: in2).asInput

            out :=
              x switch {
                case Left(x) =>
                  y switch {
                    case Left(y) =>
                      injectL(mergeInXY(x |*| y))
                    case Right(--(u)) =>
                      injectL(mergeInXT(x |*| u))
                  }
                case Right(t) =>
                  y switch {
                    case Left(y) =>
                      injectR(aux(yt(y) |*| t))
                    case Right(--(u)) =>
                      injectR(aux(u |*| t))
                  }
              }
          }
        case Right(one) =>
          one :>> crashNow(s"TODO: eliminate this path ${summon[SourcePos]}")
      }}

    def mergeFlip[T, X, Y](
      tapFlop: Y -⚬ (Y |*| X),
      mergeT: (T |*| T) -⚬ T,
    ): (YieldF[-[T], Y] |*| YieldF[T, X]) -⚬ YieldF[-[T], Y] = {
      val ft: -[-[T]] -⚬ (-[-[T]] |*| -[T]) = {
        val f0: (-[T] |*| T) -⚬ -[T] =
          λ { case u |*| t =>
            val u1 |*| u2 = u :>> contrapositive(mergeT) :>> distributeInversion
            returning(u1, t supplyTo u2)
          }
        contrapositive(f0) > distributeInversion
      }

      λ { case a |*| b =>
        a switch {
          case Left(-(a)) =>
            b switch {
              case Left(-(b)) =>
                producing { r =>
                  (a |*| b) :=
                    (injectL >>: r).asInput switch {
                      case Left(y) =>
                        val y1 |*| x = tapFlop(y)
                        injectL(y1) |*| injectL(x)
                      case Right(t) =>
                        val t1 |*| t2 = ft(t)
                        injectR(t1) |*| injectR(t2)
                    }
                }
              case Right(?(_)) =>
                producing { r =>
                  crashNow(s"TODO: eliminate this path ${summon[SourcePos]}") >>: (a |*| r)
                }
            }
          case Right(?(_)) =>
            b :>> crashNow(s"TODO: eliminate this path ${summon[SourcePos]}")
        }
      }
    }

    def mergeIn[T, X, Y](
      tapFlip: X -⚬ (X |*| Y),
      splitT: T -⚬ (T |*| T),
    ): (YieldF[T, X] |*| YieldF[-[T], Y]) -⚬ YieldF[T, X] = {
      val ft: -[T] -⚬ (-[T] |*| -[-[T]]) = {
        val f0: (T |*| -[T]) -⚬ T =
          λ { case t |*| u =>
            val t1 |*| t2 = splitT(t)
            returning(t1, t2 supplyTo u)
          }
        contrapositive(f0) > distributeInversion
      }

      λ { case a |*| b =>
        a switch {
          case Left(-(a)) =>
            b switch {
              case Left(-(b)) =>
                producing { r =>
                  (a |*| b) :=
                    (injectL >>: r).asInput switch {
                      case Left(x) =>
                        val x1 |*| y = tapFlip(x)
                        injectL(x1) |*| injectL(y)
                      case Right(t) =>
                        val t1 |*| t2 = ft(t)
                        injectR(t1) |*| injectR(t2)
                    }
                }
              case Right(?(_)) =>
                ???
            }
          case Right(?(_)) =>
            ???
        }
      }
    }

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

    def makeAbstractType[T]: Label -⚬ (ReboundType[T] |*| ReboundF[-[T], TypeEmitter[T], ReboundType[T]]) =
      TypeSkelet.makeAbstractType[-[T], TypeEmitter[T], ReboundType[T]] > fst(pack)

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

    // def mergeIn__[T](
    //   splitT: T -⚬ (T |*| T),
    //   neglectT: T -⚬ Done,
    //   zeroTypeArg: Label -⚬ (T |*| Done),
    //   tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
    //   split: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
    // ): (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] = rec { self =>
    //   par(unpack, TypeEmitter.unpack) > TypeSkelet.mergeOpWith[-[T], T, TypeEmitter[T], ReboundType[T]](
    //     split,
    //     self,
    //     tapFlip,
    //     factorOutInversion > contrapositive(splitT),
    //     pack,
    //     TypeEmitter.pack,
    //     λ { nt =>
    //       producing { case nt1 |*| tOut =>
    //         val t = nt1.asInput
    //         val t1 |*| t2 = splitT(t)
    //         tOut := returning(t1, t2 supplyTo nt)
    //       }
    //     },
    //     λ { case t |*| nt =>
    //       val t1 |*| t2 = splitT(t)
    //       returning(t1, t2 supplyTo nt)
    //     },
    //     outputApprox(neglectT),
    //     TypeEmitter.outputApprox(zeroTypeArg),
    //   )
    // }

    // def mergeIn_[T](
    //   splitT: T -⚬ (T |*| T),
    //   neglectT: T -⚬ Done,
    //   zeroTypeArg: Label -⚬ (T |*| Done),
    //   mergeOutbound: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
    //   tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
    // ): (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] =
    //   mergeIn__(
    //     splitT,
    //     neglectT,
    //     zeroTypeArg,
    //     tapFlip,
    //     split__(splitT, mergeOutbound, tapFlip),
    //   )

    // def mergeIn[T](
    //   splitT: T -⚬ (T |*| T),
    //   neglectT: T -⚬ Done,
    //   zeroTypeArg: Label -⚬ (T |*| Done),
    // ): (ReboundType[T] |*| TypeEmitter[T]) -⚬ ReboundType[T] = {
    //   val (split, mergeOutbound, tapFlip) =
    //     rec3 {
    //       (
    //         split: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
    //         mergeOutbound: (TypeEmitter[T] |*| TypeEmitter[T]) -⚬ TypeEmitter[T],
    //         tapFlip: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]),
    //       ) => (
    //         split__(splitT, mergeOutbound, tapFlip),
    //         TypeEmitter.merge_(splitT, zeroTypeArg, split),
    //         TypeEmitter.tapFlip_(splitT, split),
    //       )
    //     }

    //   println("mergeIn 1")
    //   val res = mergeIn_(
    //     splitT,
    //     neglectT,
    //     zeroTypeArg,
    //     mergeOutbound,
    //     tapFlip,
    //   )
    //   println("mergeIn 2")
    //   res
    // }

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
      val closeTParam: (Label |*| -[-[T]]) -⚬ Done =
        λ { case lbl |*| --(t) =>
          join(closeT(t) |*| Labels.neglect(lbl))
        }

      rec { self =>
        unpack > TypeSkelet.close(self, closeTParam)
      }
    }

    // def zero[T](
    //   zeroTypeArg: Label -⚬ (T |*| Done),
    // ): Label -⚬ (ReboundType[T] |*| Done) =
    //   λ { case +(label) =>
    //     val res |*| resp = makeAbstractType[T](label)
    //     res |*| (resp switch {
    //       case Left(x) =>
    //         join(TypeEmitter.close(zeroTypeArg)(x) |*| Labels.neglect(label))
    //       case Right(value) =>
    //         value switch {
    //           case Left(req) =>
    //             val --(nt) = req contramap injectR
    //             val t |*| d = zeroTypeArg(label)
    //             returning(d, t supplyTo nt)
    //           case Right(?(_)) =>
    //             label :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
    //         }
    //     })
    //   }

    def probeApprox[T](
      outputTypeParamApprox: (TParamLabel |*| -[T]) -⚬ Val[Type],
    ): (TParamLabel |*| -[ReboundType[T]]) -⚬ Val[Type] =
      λ { case label |*| nt =>
        val lbl1 |*| lbl2 = Labels.split(Labels.abstractify(label))
        val t |*| reb = makeAbstractType[T](lbl1)
        returning(
          reb switch {
            case Left(x) =>
              TypeEmitter.outputApprox(outputTypeParamApprox)(x)
                .waitFor(Labels.neglect(lbl2))
            case Right(value) =>
              value switch {
                case Left(req) =>
                  val --(nt) = req contramap injectR
                  val l = Labels.generify(lbl2)
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

    def apply1[X]: (Val[TypeTagF] |*| X) -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def apply1T[X, F[_]](F: TypeTag[F]): X -⚬ NonAbstractTypeF[X] =
      λ { x =>
        apply1(constantVal(TypeTag.toTypeFun(F)) |*| x)
      }

    def string[X]: Done -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def int[X]: Done -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def unit[X]: Done -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR

    def mismatch[X]: Val[(Type, Type)] -⚬ NonAbstractTypeF[X] =
      injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL

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
                          case Right(f |*| x) => // apply1
                            apply1(f |*| g(x))
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
                          case Right(g |*| x) => // apply1
                            val g1 |*| g2 = dsl.dup(g)
                            val x1 |*| x2 = f(x)
                            apply1(g1 |*| x1) |*| apply1(g2 |*| x2)
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
      }

    def split[X](
      splitX: X -⚬ (X |*| X),
    ): NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[X] |*| NonAbstractTypeF[X]) =
      splitMap(splitX)

    def flopMerge[Y, X]: NonAbstractTypeF[X] -⚬ (Y |*| NonAbstractTypeF[X]) =
      ???

    def flopSplit[Y, X]: NonAbstractTypeF[X] -⚬ (NonAbstractTypeF[Y] |*| NonAbstractTypeF[Y]) =
      ???

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
                                          case Right(f |*| x) => // `a` is apply1
                                            b switch {
                                              case Right(h |*| y) => // `b` is apply1
                                                ((f ** h) :>> mapVal { case (f, h) =>
                                                  if (f == h) Left(f)
                                                  else        Right((f, h))
                                                } :>> liftEither) switch {
                                                  case Left(f) =>
                                                    NonAbstractType.apply1(f |*| g(x |*| y))
                                                  case Right(fh) =>
                                                    val x1 = outputXApprox(x)
                                                    val y1 = outputYApprox(y)
                                                    // XXX: of course it is wrong to conclude from f != h that f(x) != h(y)
                                                    NonAbstractType.mismatch((fh ** (x1 ** y1)) :>> mapVal { case ((f, h), (x, y)) => (f.vmap(Left(_))(x), h.vmap(Left(_))(y)) })
                                                }
                                              case Left(b) =>
                                                NonAbstractType.mismatch(
                                                  ((f ** outputXApprox(x)) :>> mapVal { case (f, x) => f.vmap(Left(_))(x) })
                                                  ** output(outputYApprox)(injectL(injectL(injectL(injectL(injectL(b)))))),
                                                )
                                            }
                                          case Left(a) =>
                                            b switch {
                                              case Right(g |*| y) => // `b` is apply1
                                                (a |*| g |*| y) :>> crashNow(s"Not implemented (at ${summon[SourcePos]})")
                                              case Left(b) =>
                                                a switch {
                                                  case Right(x) => // `a` is string
                                                    b switch {
                                                      case Right(y) => // `b` is string
                                                        NonAbstractType.string(join(x |*| y))
                                                      case Left(b) =>
                                                        NonAbstractType.mismatch(
                                                          (x :>> constVal(Type.string))
                                                          ** output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(injectL(b)))))))
                                                        )
                                                    }
                                                  case Left(a) =>
                                                    b switch {
                                                      case Right(y) => // `b` is string
                                                        NonAbstractType.mismatch(
                                                          output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(injectL(a)))))))
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
                                                                  ** output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(injectL(injectL(b))))))))
                                                                )
                                                            }
                                                          case Left(a) =>
                                                            b switch {
                                                              case Right(y) => // `b` is int
                                                                NonAbstractType.mismatch(
                                                                  output(outputXApprox)(injectL(injectL(injectL(injectL(injectL(injectL(injectL(a))))))))
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
      }
    }

    def merge[X](
      mergeX: (X |*| X) -⚬ X,
      outputXApprox: X -⚬ Val[Type],
    ): (NonAbstractTypeF[X] |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[X] =
      mergeWith[X, X, X](mergeX, outputXApprox, outputXApprox)

    def mergeFlip[Y, X](): (NonAbstractTypeF[X] |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[Y] =
      ???

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
                          case Right(tf |*| a) => // apply1
                            (tf ** outputX(a)) :>> mapVal { case (f, a) =>
                              f.vmap(Left(_))(a)
                            }
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
                  case Right(f |*| x) => join(neglect(f) |*| closeX(x))
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
                  case Right(f |*| x) =>
                    apply1(f.waitFor(d) |*| x)
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
      }

    given junctionNonAbstractType[X](using
      X: Junction.Positive[X],
    ): Junction.Positive[NonAbstractTypeF[X]] with {
      override def awaitPosFst: (Done |*| NonAbstractTypeF[X]) -⚬ NonAbstractTypeF[X] =
        NonAbstractType.awaitPosFst[X](X.awaitPosFst)
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
      λ { t => NonAbstractType.apply1(constantVal(f) |*| t) :>> nonAbstractType }
      // val ct = compilationTarget[T]
      // import ct.Map_●
      // f.compile(Map_●)(ct.typeAlgebra, Map_●).get(Map_●, Map_●) > awaitPosFst
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

      val typeAlgebra: TypeAlgebra.Of[AbstractTypeLabel, Arr, ConcreteType[T], |*|, One] =
        new TypeAlgebra[AbstractTypeLabel, Arr] {
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
          override def abstractTypeName(name: AbstractTypeLabel): Arr[One, ConcreteType[T]] =
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
          val lbl1 |*| lbl2 = Labels.split(Labels.abstractify(label))
          val arg |*| resp = ReboundType.makeAbstractType[T](lbl1)
          returning(
            resp switch {
              case Left(x) =>
                (Labels.neglect(lbl2) |*| x) :>> TypeEmitter.awaitPosFst[T]
              case Right(value) =>
                value switch {
                  case Left(inReq) =>
                    val res |*| resp = TypeEmitter.makeAbstractType[T](lbl2)
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

    def split[T]: ConcreteType[T] -⚬ (ConcreteType[T] |*| ConcreteType[T]) =
      ???

    def isPair[T]: ConcreteType[T] -⚬ (ConcreteType[T] |+| (ConcreteType[T] |*| ConcreteType[T])) =
      unpack > dsl.either(
        NonAbstractType.isPair > |+|.lmap(nonAbstractType),
        typeParam > injectL,
      )

    def isRecCall[T]: ConcreteType[T] -⚬ (ConcreteType[T] |+| (ConcreteType[T] |*| ConcreteType[T])) =
      unpack > dsl.either(
        NonAbstractType.isRecCall > |+|.lmap(nonAbstractType),
        typeParam > injectL,
      )

    // def degenerify[T](
    //   zeroTypeArg: TParamLabel -⚬ (T |*| Done),
    // ): GenericType[T] -⚬ DegenericType =
    //   rec { self =>
    //     unpack > dsl.either(
    //       NonAbstractType.map(self) > DegenericType.nonAbstractType,
    //       λ { case lbl |*| p =>
    //         val l1 |*| l2 = Labels.dupTParam(lbl)
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
    //     Labels.toAbstractType,
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
              val lbl12 |*| lbl3 = Labels.split(lbl)
              val lbl1 |*| lbl2 = Labels.split(lbl12)
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
                    outputY(y) waitFor Labels.neglect(lbl3)
                  case Right(yld) =>
                    yld switch {
                      case Left(req) =>
                        val --(t) = req contramap injectR
                        outputT(Labels.generify(lbl3) |*| t)
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
            val l1 |*| l2 = Labels.split(lbl)
            val r1 |*| r2 = req :>> RefinementRequest.split(splitX, mergeY, tapFlop, mergeT)
            abstractType(l1 |*| r1) |*| abstractType(l2 |*| r2)
          case Left(t) =>
            t :>> NonAbstractType.split(splitX) :>> par(nonAbstractType, nonAbstractType)
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
                Labels.compare(aLabel |*| bLabel) switch {
                  case Left(label) => // labels are same => neither refines the other
                    val lbl1 |*| lbl2 = Labels.split(label)
                    val res |*| resp = makeAbstractType[-[T], X, Y](lbl1)
                    returning(
                      makeY(res),
                      resp switch {
                        case Left(x) =>
                          val x1 |*| x2 = splitX(x waitFor Labels.neglect(lbl2))
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
                                      injectL(mergeY(y1 |*| y2) waitFor Labels.neglect(lbl2)) supplyTo outReq
                                    case Right(--(t2)) =>
                                      val l1 |*| l2 = Labels.split(lbl2)
                                      val d = (Labels.show(l1) ** outputYApprox(y1) ** outputTParam(Labels.generify(l2) |*| t2)) :>> printLine { case ((l, y1), t2) =>
                                        s"label = $l, y1 = $y1, t2 = $t2"
                                      }
                                      (d |*| outReq) :>> crashWhenDone(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
                                  }
                                case Right(--(t1)) =>
                                  b switch {
                                    case Left(y2) =>
                                      (t1 |*| (y2 waitFor Labels.neglect(lbl2)) |*| outReq) :>> crashNow(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
                                    case Right(--(t2)) =>
                                      injectR(dii(mergeT(t1 |*| t2) waitFor Labels.neglect(lbl2))) supplyTo outReq
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
                        val lbl1 |*| lbl2 = Labels.split(label)
                        val x |*| resp = makeAbstractType[T, Y, X](lbl1)
                        returning(
                          resp switch {
                            case Left(y) =>
                              val y1 |*| x1 = tapFlop(y)
                              returning(
                                y1 waitFor Labels.neglect(lbl2),
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
                  makeY(nonAbstractType(y waitFor Labels.neglect(aLabel))),
                  RefinementRequest.completeWith(aReq |*| makeX(nonAbstractType(x))),
                )
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                val y |*| x = a :>> NonAbstractType.splitMap(tapFlop)
                returning(
                  makeY(nonAbstractType(y waitFor Labels.neglect(bLabel))),
                  RefinementRequest.completeWith(bReq |*| makeX(nonAbstractType(x))),
                )
              case Left(b) => // `b` is not abstract type
                makeY(nonAbstractType(NonAbstractType.merge(mergeY, outputYApprox)(a |*| b)))
            }
        }
      }
    }

    // def mergeFlip[T, Y, X](
    //   mergeX: (X |*| X) -⚬ X,
    //   splitX: X -⚬ (X |*| X),
    //   flipSplitX: X -⚬ (Y |*| Y),
    //   mergeFlipX: (X |*| X) -⚬ Y,
    //   newAbstractLink: One -⚬ (X |*| Y),
    //   instantiate: X -⚬ T,
    //   makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
    // ): (TypeSkelet[T, Y, X] |*| TypeSkelet[T, Y, X]) -⚬ TypeSkelet[-[T], X, Y] =
    //   λ { case a |*| b =>
    //     a switch {
    //       case Right(aLabel |*| aReq) => // `a` is abstract type
    //         b switch {
    //           case Right(bLabel |*| bReq) => // `b` is abstract type
    //             compareLabels(aLabel |*| bLabel) switch {
    //               case Left(label) => // labels are same => neither refines the other
    //                 val req = RefinementRequest.mergeFlip(mergeX, splitX, flipSplitX, mergeFlipX, newAbstractLink, instantiate)(aReq |*| bReq)
    //                 abstractType(label |*| req)
    //               case Right(res) =>
    //                 res switch {
    //                   case Left(+(aLabel)) =>
    //                     val req1 |*| req2 = aReq :>> RefinementRequest.flopSplit
    //                     returning(
    //                       abstractType(aLabel |*| req1),
    //                       RefinementRequest.completeWith(bReq |*| makeY(abstractType[-[T], X, Y](aLabel |*| req2))),
    //                     )
    //                   case Right(+(bLabel)) =>
    //                     val req1 |*| req2 = bReq :>> RefinementRequest.flopSplit
    //                     returning(
    //                       abstractType(bLabel |*| req1),
    //                       RefinementRequest.completeWith(aReq |*| makeY(abstractType(bLabel |*| req2))),
    //                     )
    //                 }
    //             }
    //           case Left(b) => // `b` is not abstract type
    //             val b1 |*| b2 = b :>> NonAbstractType.flopSplit[Y, X]
    //             returning(
    //               nonAbstractType(b1),
    //               RefinementRequest.completeWith(aReq |*| makeY(nonAbstractType(b2))),
    //             )
    //         }
    //       case Left(a) => // `a` is not abstract type
    //         b switch {
    //           case Right(bLabel |*| bReq) => // `b` is abstract type
    //             val a1 |*| a2 = a :>> NonAbstractType.flopSplit[Y, X]
    //             returning(
    //               nonAbstractType(a1),
    //               RefinementRequest.completeWith(bReq |*| makeY(nonAbstractType(a2))),
    //             )
    //           case Left(b) => // `b` is not abstract type
    //             nonAbstractType(NonAbstractType.mergeFlip()(a |*| b))
    //         }
    //     }
    //   }

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
                  makeX(nonAbstractType(bx waitFor Labels.neglect(aLabel))),
                  RefinementRequest.completeWith(aReq |*| makeY(nonAbstractType(by))),
                )
            }
          case Left(a) => // `a` is not abstract type
            b switch {
              case Right(bLabel |*| bReq) => // `b` is abstract type
                val ax |*| ay = a :>> NonAbstractType.splitMap[X, X, Y](tapFlipXY)
                returning(
                  makeX(nonAbstractType[T, Y, X](ax)) waitFor Labels.neglect(bLabel),
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
        Labels.compare(aLabel |*| bLabel) switch {
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
                val aLbl1 |*| aLbl2 = Labels.split(aLabel)
                val y |*| resp = makeAbstractType[-[T], X, Y](aLbl1)
                returning(
                  resp switch {
                    case Left(x) =>
                      val x1 |*| y1 = tapFlipXY(x)
                      returning(
                        x1 waitFor Labels.neglect(aLbl2),
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

    // def mergeOpWith[P, Q, Y, X](
    //   splitX: X -⚬ (X |*| X),
    //   mergeInXY: (X |*| Y) -⚬ X,
    //   tapFlopYX: Y -⚬ (Y |*| X),
    //   mergeP: (P |*| P) -⚬ P,
    //   makeX: TypeSkelet[P, Y, X] -⚬ X,
    //   makeY: TypeSkelet[Q, X, Y] -⚬ Y,
    //   tapFlipPQ: P -⚬ (P |*| Q),
    //   mergeInQP: (Q |*| P) -⚬ Q,
    //   outputXApprox: X -⚬ Val[Type],
    //   outputYApprox: Y -⚬ Val[Type],
    // )(using
    //   Junction.Positive[X],
    // ): (TypeSkelet[P, Y, X] |*| TypeSkelet[Q, X, Y]) -⚬ X =
    //   λ { case a |*| b =>
    //     a switch {
    //       case Right(aLabel |*| aReq) => // `a` is abstract type
    //         b switch {
    //           case Right(bLabel |*| bReq) => // `b` is abstract type
    //             mergeAbstractTypesOp(splitX, mergeInXY, tapFlopYX, makeX, makeY, mergeP, tapFlipPQ, mergeInQP)(
    //               (aLabel |*| aReq) |*| (bLabel |*| bReq)
    //             )
    //           case Left(b) => // `b` is not abstract type
    //             import NonAbstractType.junctionNonAbstractType
    //             val by |*| bx = b :>> NonAbstractType.splitMap[Y, Y, X](tapFlopYX)
    //             returning(
    //               makeX(nonAbstractType(bx waitFor neglect(aLabel))),
    //               RefinementRequest.completeWith(aReq |*| makeY(nonAbstractType(by))),
    //             )
    //         }
    //       case Left(a) => // `a` is not abstract type
    //         b switch {
    //           case Right(bLabel |*| bReq) => // `b` is abstract type
    //             val a1 |*| a2 = a :>> NonAbstractType.split(splitX)
    //             val x = makeX(nonAbstractType[P, Y, X](a1)) waitFor neglect(bLabel)
    //             returning(
    //               makeX(nonAbstractType(a2)),
    //               RefinementRequest.completeWith(bReq |*| x),
    //             )
    //           case Left(b) => // `b` is not abstract type
    //             makeX(nonAbstractType((a |*| b) :>> NonAbstractType.mergeWith(mergeInXY, outputXApprox, outputYApprox)))
    //         }
    //     }
    //   }

    // def mergeAbstractTypesOp[P, Q, Y, X](
    //   splitX: X -⚬ (X |*| X),
    //   mergeInXY: (X |*| Y) -⚬ X,
    //   tapFlopYX: Y -⚬ (Y |*| X),
    //   makeX: TypeSkelet[P, Y, X] -⚬ X,
    //   makeY: TypeSkelet[Q, X, Y] -⚬ Y,
    //   mergeP: (P |*| P) -⚬ P,
    //   tapFlipPQ: P -⚬ (P |*| Q),
    //   mergeInQP: (Q |*| P) -⚬ Q,
    // )(using
    //   Junction.Positive[X],
    // ): ((Label |*| RefinementRequestF[P, Y, X]) |*| (Label |*| RefinementRequestF[Q, X, Y])) -⚬ X =
    //   λ { case
    //     (aLabel |*| aReq)
    //     |*|
    //     (bLabel |*| bReq) =>
    //     Labels.compare(aLabel |*| bLabel) switch {
    //       case Left(label) => // labels are same => neither refines the other
    //         // TODO: Can it even legally happen that the same
    //         //       abstract type is being merged in opposite polarities?
    //         val x |*| resp = makeAbstractType[P, Y, X](label)
    //         returning(
    //           makeX(x),
    //           resp switch {
    //             case Left(y) =>
    //               val y1 |*| x1 = tapFlopYX(y)
    //               returning(
    //                 RefinementRequest.completeWith(aReq |*| y1),
    //                 RefinementRequest.completeWith(bReq |*| x1),
    //               )
    //             case Right(value) =>
    //               value switch {
    //                 case Left(outReq) =>
    //                   val a = RefinementRequest.decline(aReq)
    //                   val b = RefinementRequest.decline(bReq)
    //                   a switch {
    //                     case Left(x) =>
    //                       b switch {
    //                         case Left(y) =>
    //                           injectL(mergeInXY(x |*| y)) supplyTo outReq
    //                         case Right(nq) =>
    //                           (x |*| nq |*| outReq) :>> crashNow(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
    //                       }
    //                     case Right(np) =>
    //                       b switch {
    //                         case Left(y) =>
    //                           (y |*| np |*| outReq) :>> crashNow(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
    //                         case Right(nq) =>
    //                           val --(p) = outReq contramap injectR
    //                           val p1 |*| q1 = tapFlipPQ(p)
    //                           returning(
    //                             p1 supplyTo np,
    //                             q1 supplyTo nq,
    //                           )
    //                       }
    //                   }
    //                 case Right(?(_)) =>
    //                   (aReq |*| bReq) :>> crashNow(s"TODO: is this case ever used? (${summon[SourcePos]})")
    //               }
    //           },
    //         )
    //       case Right(res) =>
    //         res switch {
    //           case Left(+(aLabel)) =>
    //             val x |*| resp = makeAbstractType[P, Y, X](aLabel)
    //             returning(
    //               resp switch {
    //                 case Left(y) =>
    //                   val y1 |*| x1 = tapFlopYX(y)
    //                   returning(
    //                     x1 waitFor neglect(aLabel),
    //                     RefinementRequest.completeWith(aReq |*| y1),
    //                   )
    //                 case Right(b) =>
    //                   b switch {
    //                     case Right(?(_)) =>
    //                       (aLabel |*| aReq) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
    //                     case Left(bReq1) =>
    //                       val x |*| resp = makeAbstractType[P, Y, X](aLabel)
    //                       returning(
    //                         makeX(x),
    //                         resp switch {
    //                           case Left(y) =>
    //                             val y1 |*| x1 = tapFlopYX(y)
    //                             returning(
    //                               RefinementRequest.completeWith(aReq |*| y1),
    //                               injectL(x1) supplyTo bReq1,
    //                             )
    //                           case Right(value) =>
    //                             value switch {
    //                               case Right(?(_)) =>
    //                                 (aReq |*| bReq1) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
    //                               case Left(outReq) =>
    //                                 RefinementRequest.decline(aReq) switch {
    //                                   case Left(res) =>
    //                                     val x1 |*| x2 = splitX(res)
    //                                     returning(
    //                                       injectL(x1) supplyTo outReq,
    //                                       injectL(x2) supplyTo bReq1,
    //                                     )
    //                                   case Right(np) =>
    //                                     val --(p1) = bReq1 contramap injectR
    //                                     val --(p2) = outReq contramap injectR
    //                                     mergeP(p1 |*| p2) supplyTo np
    //                                 }
    //                             }
    //                         }
    //                       )
    //                   }
    //               },
    //               RefinementRequest.completeWith(bReq |*| makeX(x)),
    //             )
    //           case Right(+(bLabel)) =>
    //             val y |*| resp = makeAbstractType[Q, X, Y](bLabel)
    //             returning(
    //               resp switch {
    //                 case Left(x) =>
    //                   val x1 |*| x2 = splitX(x)
    //                   returning(
    //                     x1 waitFor neglect(bLabel),
    //                     RefinementRequest.completeWith(bReq |*| x2),
    //                   )
    //                 case Right(a) =>
    //                   a switch {
    //                     case Right(?(_)) =>
    //                       (bLabel |*| bReq) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
    //                     case Left(aReq1) =>
    //                       val x |*| resp = makeAbstractType[P, Y, X](bLabel)
    //                       returning(
    //                         makeX(x),
    //                         resp switch {
    //                           case Left(y) =>
    //                             val y1 |*| x1 = tapFlopYX(y)
    //                             returning(
    //                               RefinementRequest.completeWith(bReq |*| x1),
    //                               injectL(y1) supplyTo aReq1,
    //                             )
    //                           case Right(value) =>
    //                             value switch {
    //                               case Right(?(_)) =>
    //                                 (aReq1 |*| bReq) :>> crashNow(s"TODO: eliminate ${summon[SourcePos]}")
    //                               case Left(outReq) =>
    //                                 RefinementRequest.decline(bReq) switch {
    //                                   case Left(res) =>
    //                                     val y1 |*| x1 = tapFlopYX(res)
    //                                     returning(
    //                                       injectL(y1) supplyTo aReq1,
    //                                       injectL(x1) supplyTo outReq,
    //                                     )
    //                                   case Right(nq) =>
    //                                     val --(p) = outReq contramap injectR
    //                                     val --(q) = aReq1 contramap injectR
    //                                     mergeInQP(q |*| p) supplyTo nq
    //                                 }
    //                             }
    //                         }
    //                       )
    //                   }
    //               },
    //               RefinementRequest.completeWith(aReq |*| makeY(y)),
    //             )
    //         }
    //     }
    //   }

    // def mergeIn[T, Y, X](
    //   splitX: X -⚬ (X |*| X),
    //   mergeY: (Y |*| Y) -⚬ Y,
    //   mergeInXY: (X |*| Y) -⚬ X,
    //   mergeInXT: (X |*| T) -⚬ X,
    //   tapFlop: Y -⚬ (Y |*| X),
    //   yt: Y -⚬ T,
    //   mergeT: (T |*| T) -⚬ T,
    //   makeX: TypeSkelet[  T , Y, X] -⚬ X,
    //   makeY: TypeSkelet[-[T], X, Y] -⚬ Y,
    //   outputXApprox: X -⚬ Val[Type],
    //   outputYApprox: Y -⚬ Val[Type],
    // )(using
    //   Junction.Positive[X],
    // ): (TypeSkelet[T, Y, X] |*| TypeSkelet[-[T], X, Y]) -⚬ TypeSkelet[T, Y, X] =
    //   λ { case a |*| b =>
    //     a switch {
    //       case Right(aLabel |*| aReq) => // `a` is abstract type
    //         b switch {
    //           case Right(bLabel |*| bReq) => // `b` is abstract type
    //             compareLabels(aLabel |*| bLabel) switch {
    //               case Left(label) => // labels are same => neither refines the other
    //                 val req = (aReq |*| bReq) :>> RefinementRequest.mergeIn(tapFlop, mergeInXY, mergeInXT, yt, mergeT)
    //                 abstractType(label |*| req)
    //               case Right(res) =>
    //                 res switch {
    //                   case Left(+(aLabel)) =>
    //                     val req1 |*| req2 = aReq :>> RefinementRequest.split(splitX, mergeY, tapFlop, mergeT)
    //                     returning(
    //                       abstractType(aLabel |*| req1),
    //                       RefinementRequest.completeWith(bReq |*| makeX(abstractType[T, Y, X](aLabel |*| req2))),
    //                     )
    //                   case Right(+(bLabel)) =>
    //                     val req1 |*| req2 = bReq :>> RefinementRequest.tapFlop(splitX, mergeInXY, tapFlop, mergeT)
    //                     returning(
    //                       abstractType(bLabel |*| req2),
    //                       RefinementRequest.completeWith(aReq |*| makeY(abstractType(bLabel |*| req1))),
    //                     )
    //                 }
    //             }
    //           case Left(b) => // `b` is not abstract type
    //             import NonAbstractType.junctionNonAbstractType
    //             val by |*| bx = b :>> NonAbstractType.splitMap[Y, Y, X](tapFlop)
    //             returning(
    //               nonAbstractType(bx waitFor neglect(aLabel)),
    //               RefinementRequest.completeWith(aReq |*| makeY(nonAbstractType(by))),
    //             )
    //         }
    //       case Left(a) => // `a` is not abstract type
    //         b switch {
    //           case Right(bLabel |*| bReq) => // `b` is abstract type
    //             val a1 |*| a2 = a :>> NonAbstractType.split(splitX)
    //             val x = makeX(nonAbstractType[T, Y, X](a1)) waitFor neglect(bLabel)
    //             returning(
    //               nonAbstractType(a2),
    //               RefinementRequest.completeWith(bReq |*| x),
    //             )
    //           case Left(b) => // `b` is not abstract type
    //             nonAbstractType((a |*| b) :>> NonAbstractType.mergeWith(mergeInXY, outputXApprox, outputYApprox))
    //         }
    //     }
    //   }

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
            val lbl1 |*| lbl2 = Labels.split(label)
            val (out2 |*| resp2) = makeAbstractType[T, Y, X](lbl1)
            resp2 switch {
              case Left(y) =>
                val y1 |*| x1 = tapFlop(y)
                returning(
                  y1 |*| (makeX(out2) waitFor Labels.neglect(lbl2)),
                  RefinementRequest.completeWith(req |*| x1)
                )
              case Right(value) =>
                value switch {
                  case Left(outReq2) =>
                    val (out1 |*| resp1) = makeAbstractType[-[T], X, Y](lbl2)
                    resp1 switch {
                      case Left(x) =>
                        val x1 |*| x2 = splitX(x)
                        returning(
                          makeY(out1) |*| makeX(out2),
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
                                  makeY(out1) |*| makeX(out2),
                                  injectL(y1) supplyTo outReq1,
                                  injectL(x1) supplyTo outReq2,
                                )
                              case Right(--(t1)) =>
                                val --(t2) = outReq2 contramap injectR
                                val t = mergeT(t1 |*| t2)
                                returning(
                                  makeY(out1) |*| makeX(out2),
                                  injectR(dii(t)) supplyTo outReq1,
                                )
                            }
                          case Right(?(_)) =>
                            (out1 |*| out2 |*| outReq2 |*| req) :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
                        }
                    }
                  case Right(?(_)) =>
                    (lbl2 |*| out2 |*| req) :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
                }
            }
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
      Junction.Positive[Y],
    ): TypeSkelet[T, Y, X] -⚬ (X |*| Y) =
      λ { t =>
        t switch {
          case Right(label |*| req) => // abstract type
            val lbl1 |*| lbl2 = Labels.split(label)
            val out2 |*| resp2 = makeAbstractType[-[T], X, Y](lbl1)
            resp2 switch {
              case Left(x) =>
                val x1 |*| y1 = tapFlip(x)
                returning(
                  x1 |*| (makeY(out2) waitFor Labels.neglect(lbl2)),
                  RefinementRequest.completeWith(req |*| y1),
                )
              case Right(value) =>
                value switch {
                  case Left(outReq2) =>
                    val out1 |*| resp1 = makeAbstractType[T, Y, X](lbl2)
                    returning(
                      makeX(out1) |*| makeY(out2),
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
                    (lbl2 |*| req |*| out2) :>> crashNow(s"TODO: eliminate? (at ${summon[SourcePos]})")
                }
            }
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
            case Left(x)   => outputX(x) waitFor Labels.neglect(label)
            case Right(nt) => outputNegT(Labels.generify(label) |*| nt)
          }
        case Left(x) =>
          NonAbstractType.output(outputX)(x)
      }}

    def close[T, Y, X](
      neglectX: X -⚬ Done,
      closeTParam: (Label |*| -[T]) -⚬ Done,
    ): TypeSkelet[T, Y, X] -⚬ Done =
      λ { _ switch {
        case Right(label |*| req) => // abstract type
          RefinementRequest.decline(req) switch {
            case Left(x)   =>
              join(neglectX(x) |*| Labels.neglect(label))
            case Right(nt) =>
              closeTParam(label |*| nt)
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
                .waitFor(Labels.neglect(label))
            case Right(nt) =>
              outputTParamApprox(Labels.generify(label) |*| nt)
          }
        case Left(x) =>
          NonAbstractType.output(outputXApprox)(x)
      }}

    def generify[T, Y, X](
      wrapX: X -⚬ ConcreteType[T],
    ): TypeSkelet[T, Y, X] -⚬ ConcreteType[T] = {
      import ConcreteType.junctionConcreteType

      dsl.either(
        NonAbstractType.map(wrapX) > ConcreteType.nonAbstractType,
        λ { case lbl |*| req =>
          RefinementRequest.decline(req) switch {
            case Left(x)   => wrapX(x) waitFor Labels.neglect(lbl)
            case Right(nt) => ConcreteType.typeParam(Labels.generify(lbl) |*| nt)
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

    def nonAbstractType[T]: NonAbstractTypeF[TypeEmitter[T]] -⚬ TypeEmitter[T] =
      TypeSkelet.nonAbstractType > pack

    def makeAbstractType[T]: Label -⚬ (TypeEmitter[T] |*| ReboundF[T, ReboundType[T], TypeEmitter[T]]) =
      TypeSkelet.makeAbstractType[T, ReboundType[T], TypeEmitter[T]] > fst(pack)

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
      TypeSkelet.newAbstractType[T, ReboundType[T], TypeEmitter[T]](
        TypeEmitter.split(mergeT, outputT),
        ReboundType.merge(mergeT, outputT),
        ReboundType.tapFlop(mergeT, outputT),
        mergeT,
        ReboundType.output(outputT),
        outputT,
      )
        > λ { case a |*| t |*| b => pack(a) |*| t |*| pack(b) }

    def expectPair[T]: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      throw NotImplementedError(s"at ${summon[SourcePos]}")

    def expectRecCall[T]: TypeEmitter[T] -⚬ (TypeEmitter[T] |*| TypeEmitter[T]) =
      throw NotImplementedError(s"at ${summon[SourcePos]}")

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

    def tapFlip__[T](
      splitT: T -⚬ (T |*| T),
      splitRebound: ReboundType[T] -⚬ (ReboundType[T] |*| ReboundType[T]),
    ): TypeEmitter[T] -⚬ (TypeEmitter[T] |*| ReboundType[T]) = {
      import ReboundType.junctionReboundType

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

    // def close[T](
    //   closeTParam: (TParamLabel |*| -[T]) -⚬ Done,
    // ): TypeEmitter[T] -⚬ Done =
    //   rec { self =>
    //     unpack > TypeSkelet.close(self, closeTParam)
    //   }

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

  def inferTypes[A, B](f: Fun[A, B]): One -⚬ Val[TypedFun[A, B]] = {
    println(s"inferTypes($f)")
    val t0 = System.currentTimeMillis()

    given VarGen[State[Int, *], AbstractTypeLabel] with {
      override def newVar: State[Int, AbstractTypeLabel] =
        State(n => (n+1, AbstractTypeLabel(n)))
    }

    val closeTParam: (TParamLabel |*| -[Done]) -⚬ Done =
      λ { case lbl |*| nd =>
        returning(
          Labels.neglectTParam(lbl),
          constant(done) supplyTo nd,
        )
      }

    val res =
    reconstructTypes[Done, A, B, State[Int, *]](f)(
      join,
      fork,
      fst(Labels.toAbstractType) > awaitPosSnd,
      λ { case lbl |*| nd => returning(Labels.toAbstractType(lbl), constant(done) supplyTo nd) },
      id[Done],
      TypeEmitter.generify,
    )
      .map { prg =>
        prg > λ { case a |*| f |*| b =>
          f
            .waitFor(a :>> ConcreteType.close(closeTParam))
            .waitFor(b :>> ConcreteType.close(closeTParam))
        }
      }
      .run(0)

    val t1 = System.currentTimeMillis()
    println(s"inferTypes assembly took ${t1 - t0}ms")
    res
  }

  def reconstructTypes[T, A, B, M[_]](f: Fun[A, B])(
    mergeT: (T |*| T) -⚬ T,
    splitT: T -⚬ (T |*| T),
    outputT: (TParamLabel |*| T) -⚬ Val[Type],
    outputTParam: (TParamLabel |*| -[T]) -⚬ Val[Type],
    neglectT: T -⚬ Done,
    // zeroTypeArg: Label -⚬ (T |*| Done),
    // outputTypeParamApprox: (TParamLabel |*| -[T]) -⚬ Val[Type],
    generify: TypeEmitter[T] -⚬ GenericType[T],
    // degenerify: GenericType[T] -⚬ DegenericType,
  )(using
    gen: VarGen[M, AbstractTypeLabel],
    M: Monad[M],
    T: Junction.Positive[T],
  ): M[One -⚬ (ConcreteType[T] |*| Val[TypedFun[A, B]] |*| ConcreteType[T])] = {
    println(s"reconstructTypes($f)")
    import ConcreteType.{apply1T, fixT, int, isPair, isRecCall, pair, recCall, string}
    import ReboundType.junctionReboundType

    def reconstructTypes[A, B](f: Fun[A, B]): M[One -⚬ (ConcreteType[ReboundType[T]] |*| Val[TypedFun[A, B]] |*| ConcreteType[ReboundType[T]])] =
      TypeInference.reconstructTypes[ReboundType[T], A, B, M](f)(
        ReboundType.merge(mergeT, outputT),
        ReboundType.split(splitT, outputTParam),
        fst(Labels.neglectTParam) > ReboundType.awaitPosFst > ReboundType.output(outputT),
        // ReboundType.zero(zeroTypeArg),
        ReboundType.probeApprox(outputTParam),
        ReboundType.close(neglectT),
        TypeEmitter.generify[ReboundType[T]],
        // ConcreteType.degenerify(ReboundType.zero(zeroTypeArg)),
      )

    def newAbstractType: Label -⚬ (TypeEmitter[T] |*| Val[Type] |*| TypeEmitter[T]) =
      TypeEmitter.newAbstractType(mergeT, outputT)

    def newAbstractTypeG(v: AbstractTypeLabel)(using
      SourcePos,
      LambdaContext,
    ): $[ConcreteType[T] |*| Val[Type] |*| ConcreteType[T]] =
      newAbstractType(Labels.make(v)) > λ { case a |*| t |*| b =>
        generify(a) |*| t |*| generify(b)
      }

    def newTypeParam: Label -⚬ (Val[Type] |*| ConcreteType[T]) =
      λ { label =>
        val l1 |*| l2 = Labels.split(label)
        val nt |*| t = constant(demand[T])
        outputT(Labels.generify(l1) |*| t) |*| ConcreteType.typeParam(Labels.generify(l2) |*| nt)
      }

    def merge: (ConcreteType[ReboundType[T]] |*| ConcreteType[ReboundType[T]]) -⚬ ConcreteType[T] =
      ConcreteType.merge(splitT, outputTParam)

    def output: ConcreteType[T] -⚬ Val[Type] =
      ConcreteType.output(outputTParam)

    val lower: ConcreteType[ReboundType[T]] -⚬ ConcreteType[T] =
      ConcreteType.abstractify[T] > generify

    f.value match {
      case FunT.IdFun() =>
        for {
          v <- gen.newVar
        } yield
          λ.? { _ =>
            val a |*| t |*| b = newAbstractTypeG(v)
            a |*| (t :>> mapVal(TypedFun.Id(_))) |*| b
          }
      case FunT.AndThen(f, g) =>
        for {
          tf <- reconstructTypes(f)
          tg <- reconstructTypes(g)
        } yield
          λ.* { one =>
            val a |*| f |*| x1 = tf(one)
            val x2 |*| g |*| b = tg(one)
            val x = output(merge(x1 |*| x2))
            val h = (f ** x ** g) :>> mapVal { case ((f, x), g) => TypedFun.andThen(f, x, g) }
            lower(a) |*| h |*| lower(b)
          }
      case FunT.Par(f1, f2) =>
        for {
          tf1 <- reconstructTypes(f1)
          tf2 <- reconstructTypes(f2)
        } yield
          λ.* { one =>
            val a1 |*| f1 |*| b1 = tf1(one)
            val a2 |*| f2 |*| b2 = tf2(one)
            val a = pair(a1 |*| a2)
            val b = pair(b1 |*| b2)
            val f = (f1 ** f2) :>> mapVal { case (f1, f2) => TypedFun.par(f1, f2) }
            lower(a) |*| f |*| lower(b)
          }
      case _: FunT.AssocLR[arr, a, b, c] =>
        for {
          a <- gen.newVar
          b <- gen.newVar
          c <- gen.newVar
        } yield {
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractTypeG(a)
            val b1 |*| tb |*| b2 = newAbstractTypeG(b)
            val c1 |*| tc |*| c2 = newAbstractTypeG(c)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.assocLR[a, b, c](a, b, c) }
            val in  = pair(pair(a1 |*| b1) |*| c1)
            val out = pair(a2 |*| pair(b2 |*| c2))
            in |*| f |*| out
          }
        }
      case _: FunT.AssocRL[arr, a, b, c] =>
        for {
          a <- gen.newVar
          b <- gen.newVar
          c <- gen.newVar
        } yield {
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractTypeG(a)
            val b1 |*| tb |*| b2 = newAbstractTypeG(b)
            val c1 |*| tc |*| c2 = newAbstractTypeG(c)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.assocRL[a, b, c](a, b, c) }
            val in  = pair(a1 |*| pair(b1 |*| c1))
            val out = pair(pair(a2 |*| b2) |*| c2)
            in |*| f |*| out
          }
        }
      case _: FunT.Swap[arr, a, b] =>
        for {
          a <- gen.newVar
          b <- gen.newVar
        } yield {
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractTypeG(a)
            val b1 |*| tb |*| b2 = newAbstractTypeG(b)
            val f = (ta ** tb) :>> mapVal { case (a, b) => TypedFun.swap[a, b](a, b) }
            val in  = pair(a1 |*| b1)
            val out = pair(b2 |*| a2)
            in |*| f |*| out
          }
        }
      case FunT.EitherF(f, g) =>
        for {
          tf <- reconstructTypes(f)
          tg <- reconstructTypes(g)
        } yield
          λ.* { one =>
            val a1 |*| f |*| b1 = tf(one)
            val a2 |*| g |*| b2 = tg(one)
            val a = ConcreteType.either(a1 |*| a2)
            val b = merge(b1 |*| b2)
            val h = (f ** g) :>> mapVal { case (f, g) => TypedFun.either(f, g) }
            lower(a) |*| h |*| b
          }
      case _: FunT.InjectL[arr, l, r] =>
        for {
          l <- gen.newVar
          r <- gen.newVar
        } yield
          λ.? { _ =>
            val l1 |*| lt |*| l2 = newAbstractTypeG(l)
            val        rt |*| r2 = newTypeParam(Labels.make(r))
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectL[l, r](lt, rt) }
            val b = ConcreteType.either(l2 |*| r2)
            (l1 |*| f |*| b)
          }
      case _: FunT.InjectR[arr, l, r] =>
        for {
          l <- gen.newVar
          r <- gen.newVar
        } yield
          λ.? { _ =>
            val        lt |*| l2 = newTypeParam(Labels.make(l))
            val r1 |*| rt |*| r2 = newAbstractTypeG(r)
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectR[l, r](lt, rt) }
            val b = ConcreteType.either(l2 |*| r2)
            (r1 |*| f |*| b)
          }
      case FunT.Distribute() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case f: FunT.FixF[arr, f] =>
        M.pure(
          λ.* { one =>
            val fixF = fixT[T, f](f.f)(one)
            val fFixF = apply1T(f.f)(fixT[T, f](f.f)(one))
            val tf = constantVal(TypedFun.fix[f](TypeTag.toTypeFun(f.f).vmap(Left(_))))
            fFixF |*| tf |*| fixF
          }
        )
      case f: FunT.UnfixF[arr, f] =>
        M.pure(
          λ.* { one =>
            val fixF = fixT[T, f](f.f)(one)
            val fFixF = apply1T(f.f)(fixT[T, f](f.f)(one))
            val tf = constantVal(TypedFun.unfix[f](TypeTag.toTypeFun(f.f).vmap(Left(_))))
            fixF |*| tf |*| fFixF
          }
        )
      case FunT.Rec(f) =>
        for {
          tf <- reconstructTypes(f)
        } yield
          tf > λ { case aba |*| f |*| b1 =>
            isPair(aba) switch {
              case Right(ab |*| a1) =>
                isRecCall(ab) switch {
                  case Right(a0 |*| b0) =>
                    val a = merge(a0 |*| a1)
                    val b = merge(b0 |*| b1)
                    val h = f :>> mapVal { TypedFun.rec(_) }
                    a |*| h |*| b
                  case Left(ab) =>
                    (ab |*| f |*| a1 |*| b1) :>> crashNow(s"TODO (${summon[SourcePos]})")
                }
              case Left(aba) =>
                import scala.concurrent.duration._
                val d = (f ** output(lower(aba)) ** output(lower(b1)))
                  :>> printLine { case ((f, aba), b) =>
                    s"FUNCTION=${scala.util.Try(f.toString)}, IN-TYPE=$aba, OUT-TYPE=$b"
                  }
                d :>> fork :>> crashWhenDone(s"TODO (${summon[SourcePos]})")
                // (d |*| b1) :>> crashNow(s"TODO (${summon[SourcePos]})")
            }
          }
      case _: FunT.Recur[arr, a, b] =>
        for {
          va <- gen.newVar
          vb <- gen.newVar
        } yield
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractTypeG(va)
            val b1 |*| tb |*| b2 = newAbstractTypeG(vb)
            val tf = (ta ** tb) :>> mapVal { case (ta, tb) => TypedFun.recur[a, b](ta, tb) }
            val tIn = pair(recCall(a1 |*| b1) |*| a2)
            tIn |*| tf |*| b2
          }
      case FunT.ConstInt(n) =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FunT.AddInts() =>
        M.pure(
          λ.? { one =>
            val a1 = constant(done > int[T])
            val a2 = constant(done > int[T])
            val b  = constant(done > int[T])
            val tf = constantVal(TypedFun.addInts)
            pair(a1 |*| a2) |*| tf |*| b
          }
        )
      case FunT.IntToString() =>
        M.pure(
          λ.* { one =>
            val a = done(one) :>> int[T]
            val b = done(one) :>> string[T]
            val tf = constantVal(TypedFun.intToString)
            a |*| tf |*| b
          }
        )
    }
  }
}
