package libretto.typology.toylang.typeinfer

import libretto.lambda.UnhandledCase
import libretto.lambda.util.SourcePos
import libretto.scaletto.StarterKit.*
import libretto.scaletto.StarterKit.$.*
import libretto.scaletto.StarterKit
import libretto.typology.toylang.terms.TypedFun.Type
import libretto.typology.toylang.types.TypeTag
import libretto.typology.toylang.types.{AbstractTypeLabel, ScalaTypeParam}
import libretto.typology.toylang.typeinfer.Tools.ToolsImpl.NonAbstractTypeF
import libretto.typology.toylang.typeinfer.Tools.ToolsImpl.NonAbstractType
import scala.annotation.targetName
// import libretto.typology.toylang.types.{AbstractTypeLabel, ScalaTypeParam, TypeAlgebra, TypeTag}

trait TypeInferencer extends Tools {
  type Tp
  type TypeOutlet

  override type OutboundType = Tp
  override type OutwardType = TypeOutlet
  override type MergeableType = Tp
  override type SplittableType = Tp

  def merge: (Tp |*| Tp) -⚬ Tp
  def split: Tp -⚬ (Tp |*| Tp)
}

trait TypeOps[F[_]] {
  def map[A, B](f: A -⚬ B): F[A] -⚬ F[B]

  // TODO: eliminate the output parameter
  def merge[A](f: (A |*| A) -⚬ A, output: A -⚬ Val[Type]): (F[A] |*| F[A]) -⚬ F[A]

  def split[A](f: A -⚬ (A |*| A)): F[A] -⚬ (F[A] |*| F[A])

  def output[A](f: A -⚬ Val[Type]): F[A] -⚬ Val[Type]

  def close[A](f: A -⚬ Done): F[A] -⚬ Done

  def awaitPosFst[A](f: (Done |*| A) -⚬ A): (Done |*| F[A]) -⚬ F[A]

  def pair[A]: (A |*| A) -⚬ F[A]
  def recCall[A]: (A |*| A) -⚬ F[A]

  def isPair[A]: F[A] -⚬ (F[A] |+| (A |*| A))
  def isRecCall[A]: F[A] -⚬ (F[A] |+| (A |*| A))
}

object TypeInferencer {

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

  val typeOps: TypeOps[NonAbstractTypeF] =
    new TypeOps[NonAbstractTypeF] {
      override def map[A, B](f: A -⚬ B): NonAbstractTypeF[A] -⚬ NonAbstractTypeF[B] =
        NonAbstractType.map(f)

      override def merge[A](
        f: (A |*| A) -⚬ A,
        output: A -⚬ Val[Type],
      ): (NonAbstractTypeF[A] |*| NonAbstractTypeF[A]) -⚬ NonAbstractTypeF[A] =
        NonAbstractType.merge(f, output)

      override def split[A](f: A -⚬ (A |*| A)): NonAbstractTypeF[A] -⚬ (NonAbstractTypeF[A] |*| NonAbstractTypeF[A]) =
        NonAbstractType.split(f)

      override def output[A](f: A -⚬ Val[Type]): NonAbstractTypeF[A] -⚬ Val[Type] =
        NonAbstractType.output(f)

      override def close[A](f: A -⚬ Done): NonAbstractTypeF[A] -⚬ Done =
        NonAbstractType.close(f)

      override def awaitPosFst[A](f: (Done |*| A) -⚬ A): (Done |*| NonAbstractTypeF[A]) -⚬ NonAbstractTypeF[A] =
        NonAbstractType.awaitPosFst(f)

      override def pair[A]: (A |*| A) -⚬ NonAbstractTypeF[A] =
        NonAbstractType.pair

      override def isPair[A]: NonAbstractTypeF[A] -⚬ (NonAbstractTypeF[A] |+| (A |*| A)) =
        NonAbstractType.isPair

      override def recCall[A]: (A |*| A) -⚬ NonAbstractTypeF[A] =
        NonAbstractType.recCall

      override def isRecCall[A]: NonAbstractTypeF[A] -⚬ (NonAbstractTypeF[A] |+| (A |*| A)) =
        NonAbstractType.isRecCall
    }

  def instance: TypeInferencer =
    TypeInferencerImpl[NonAbstractTypeF, Done](
      labels,
      typeOps,
      splitTypeParam = fork,
      typeParamLink = labels.neglect > fork,
      typeParamTap = labels.unwrapOriginal > mapVal(x => Type.abstractType(x)) > signalPosFst,
      outputTypeParam = fst(labels.unwrapOriginal > mapVal(x => Type.abstractType(x))) > awaitPosSnd,
      closeTypeParam = fst(labels.neglect) > join,
    )
}

object TypeInferencerImpl {
  def apply[F[_], P](
    labels: Labels[Either[ScalaTypeParam, AbstractTypeLabel]],
    F: TypeOps[F],
    splitTypeParam: P -⚬ (P |*| P),
    typeParamLink: labels.Label -⚬ (P |*| P),
    typeParamTap: labels.Label -⚬ (P |*| Val[Type]),
    outputTypeParam: (labels.Label |*| P) -⚬ Val[Type],
    closeTypeParam: (labels.Label |*| P) -⚬ Done,
  ): TypeInferencerImpl[F, P, labels.type] =
    new TypeInferencerImpl(
      labels,
      F,
      splitTypeParam,
      typeParamLink,
      typeParamTap,
      outputTypeParam,
      closeTypeParam,
    )
}

class TypeInferencerImpl[
  F[_],
  P,
  Lbls <: Labels[Either[ScalaTypeParam, AbstractTypeLabel]], // TODO: make a type parameter
](
  val labels: Lbls,
  F: TypeOps[F],
  // mergeTypeParams: (P |*| P) -⚬ P,
  splitTypeParam: P -⚬ (P |*| P),
  typeParamLink: labels.Label -⚬ (P |*| P),
  typeParamTap: labels.Label -⚬ (P |*| Val[Type]),
  outputTypeParam: (labels.Label |*| P) -⚬ Val[Type],
  closeTypeParam: (labels.Label |*| P) -⚬ Done,
) extends TypeInferencer { self =>

  override type Label = labels.Label

  object Refinement {
    opaque type Request[T] = -[Response[T]]
    opaque type Response[T] = T |+| -[T |+| P]

    def makeRequest[T]: One -⚬ (Request[T] |*| Response[T]) =
      forevert

    extension [T](req: $[Request[T]]) {
      def grant(t: $[T])(using SourcePos, LambdaContext): $[One] =
        injectL(t) supplyTo req

      def decline(using SourcePos, LambdaContext): $[T |+| P] =
        die(req contramap injectR)

      @targetName("closeRefinementRequest")
      def close(lbl: $[Label], f: T -⚬ Done)(using SourcePos, LambdaContext): $[Done] =
        req.decline switch {
          case Left(t) =>
            join(f(t) |*| labels.neglect(lbl))
          case Right(p) =>
            closeTypeParam(lbl |*| p)
        }
    }

    extension [T](resp: $[Response[T]]) {
      def toEither: $[T |+| -[T |+| P]] =
        resp

      @targetName("closeRefinementResponse")
      def close(lbl: $[Label], f: T -⚬ Done)(using SourcePos, LambdaContext): $[Done] =
        resp switch {
          case Left(t) =>
            join(f(t) |*| labels.neglect(lbl))
          case Right(req) =>
            val p |*| t = typeParamTap(lbl)
            returning(
              neglect(t),
              injectR(p) supplyTo req,
            )
        }
    }
  }

  object AbsTp {
    type Proper[T] = Label |*| Refinement.Request[T]
    type Prelim[T] = Label |*| T
  }
  type AbsTp[T] = AbsTp.Proper[T] |+| AbsTp.Prelim[T]

  override type Tp = Rec[[Tp] =>> AbsTp[Tp] |+| F[Tp]]
  override type TypeOutlet = Rec[[X] =>> (Label |*| P) |+| F[X]]

  private def pack: (AbsTp[Tp] |+| F[Tp]) -⚬ Tp =
    dsl.pack[[X] =>> AbsTp[X] |+| F[X]]

  private def unpack: Tp -⚬ (AbsTp[Tp] |+| F[Tp]) =
    dsl.unpack[[X] =>> AbsTp[X] |+| F[X]]

  def abstractType: (Label |*| Refinement.Request[Tp]) -⚬ Tp =
    injectL > injectL > pack

  def preliminary: (Label |*| Tp) -⚬ Tp =
    injectR > injectL > pack

  def concreteType: F[Tp] -⚬ Tp =
    injectR > pack

  def makeAbstractType: Label -⚬ (Tp |*| Refinement.Response[Tp]) =
    introSnd(Refinement.makeRequest) > assocRL > fst(abstractType)

  override def merge: (Tp |*| Tp) -⚬ Tp =
    rec { self =>
      merge_(split_(self))
    }

  override def split: Tp -⚬ (Tp |*| Tp) =
    rec { self =>
      split_(merge_(self))
    }

  private def merge_(
    split: Tp -⚬ (Tp |*| Tp),
  ): (Tp |*| Tp) -⚬ Tp = rec { self =>
    par(unpack, unpack) > λ { case a |*| b =>
      a switch {
        case Left(a) =>
          b switch {
            case Left(b) =>
              mergeAbstractTypes(self, split)(a |*| b)
            case Right(fb) =>
              mergeConcreteAbstract(self, split)(fb |*| a)
          }
        case Right(fa) =>
          b switch {
            case Left(b) =>
              mergeConcreteAbstract(self, split)(fa |*| b)
            case Right(fb) =>
              concreteType(F.merge(self, output)(fa |*| fb))
          }
      }
    }
  }

  private def mergeAbstractTypes(
    merge: (Tp |*| Tp) -⚬ Tp,
    split: Tp -⚬ (Tp |*| Tp),
  ): (AbsTp[Tp] |*| AbsTp[Tp]) -⚬ Tp =
    λ { case a |*| b =>
      a switch {
        case Left(a) =>
          b switch {
            case Left(b) =>
              mergeAbstractTypesProper(merge, split)(a |*| b)
            case Right(b) =>
              mergeAbstractProperPreliminary(merge, split)(a |*| b)
          }
        case Right(a) =>
          b switch {
            case Left(b) =>
              (a |*| b) :>> crashNow(s"TODO (at ${summon[SourcePos]})")
            case Right(b) =>
              mergePreliminaries(merge)(a |*| b)
          }
      }
    }

  /** Ignores the input via a (local) deadlock. */
  private val hackyDiscard: Done -⚬ One =
    λ { d0 =>
      val n |*| d1 = constant(lInvertSignal)
      val d = join(d0 |*| d1)
      rInvertSignal(d |*| n)
    }

  private def mergeAbstractTypesProper(
    merge: (Tp |*| Tp) -⚬ Tp,
    split: Tp -⚬ (Tp |*| Tp),
  ): (AbsTp.Proper[Tp] |*| AbsTp.Proper[Tp]) -⚬ Tp =
    λ { case (aLbl |*| aReq) |*| (bLbl |*| bReq) =>
      labels.compare(aLbl |*| bLbl) switch {
        case Left(lbl) =>
          // // labels are same => neither refines the other
          // val res |*| resp = makeAbstractType(lbl)
          // returning(
          //   res,
          //   resp.toEither switch {
          //     case Left(t) =>
          //       val t1 |*| t2 = split(t)
          //       returning(
          //         aReq grant t1,
          //         bReq grant t2,
          //       )
          //     case Right(req) =>
          //       val a = aReq.decline
          //       val b = bReq.decline
          //       a switch {
          //         case Left(a) =>
          //           b switch {
          //             case Left(b) =>
          //               injectL(merge(a |*| b)) supplyTo req
          //             case Right(q) =>
          //               (a |*| q |*| req) :>> crashNow(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
          //           }
          //         case Right(p) =>
          //           b switch {
          //             case Left(b) =>
          //               (p |*| b |*| req) :>> crashNow(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
          //             case Right(q) =>
          //               injectR(mergeTypeParams(p |*| q)) supplyTo req
          //           }
          //       }
          //   }
          // )

          // Labels are same, i.e. both refer to the same type.
          // Propagate one (arbitrary) of them, close the other.
          val aLbl |*| bLbl = labels.split(lbl)
          returning(
            abstractType(aLbl |*| aReq),
            hackyDiscard(bReq.close(bLbl, close)),
          )

        case Right(res) =>
          def go: (Label |*| Refinement.Request[Tp] |*| Refinement.Request[Tp]) -⚬ Tp =
            λ { case aLbl |*| aReq |*| bReq =>
              val aLbl1 |*| aLbl2 = labels.split(aLbl)
              val out1 |*| resp1 = makeAbstractType(aLbl1)
              val out2 |*| resp2 = makeAbstractType(aLbl2)
              returning(
                out1,
                bReq grant out2,
                resp1.toEither switch {
                  case Left(t1) =>
                    resp2.toEither switch {
                      case Left(t2) =>
                        aReq grant merge(t1 |*| t2)
                      case Right(req2) =>
                        val t11 |*| t12 = split(t1)
                        returning(
                          aReq grant t11,
                          injectL(t12) supplyTo req2,
                        )
                    }
                  case Right(req1) =>
                    resp2.toEither switch {
                      case Left(t2) =>
                        val t21 |*| t22 = split(t2)
                        returning(
                          aReq grant t21,
                          injectL(t22) supplyTo req1,
                        )
                      case Right(req2) =>
                        aReq.decline switch {
                          case Left(t) =>
                            val t1 |*| t2 = split(t)
                            returning(
                              injectL(t1) supplyTo req1,
                              injectL(t2) supplyTo req2,
                            )
                          case Right(p) =>
                            val p1 |*| p2 = splitTypeParam(p)
                            returning(
                              injectR(p1) supplyTo req1,
                              injectR(p2) supplyTo req2,
                            )
                        }
                    }
                },
              )
            }

          res switch {
            case Left(aLbl) =>
              go(aLbl |*| aReq |*| bReq)
            case Right(bLbl) =>
              go(bLbl |*| bReq |*| aReq)
          }
      }
    }

  private def mergeAbstractProperPreliminary(
    merge: (Tp |*| Tp) -⚬ Tp,
    split: Tp -⚬ (Tp |*| Tp),
  ): (AbsTp.Proper[Tp] |*| AbsTp.Prelim[Tp]) -⚬ Tp =
    λ { case (aLbl |*| aReq) |*| (bLbl |*| b) =>
      val bl1 |*| bl2 = labels.split(bLbl)
      labels.compare(aLbl |*| bl1) switch {
        case Left(lbl) =>
          // Labels are equal, refer to the same type.
          // Close the refinement request, propagate the preliminary.
          returning(
            b,
            hackyDiscard(aReq.close(lbl, close) waitFor labels.neglect(bl2)),
          )
        case Right(res) =>
          res switch {
            case Left(aLbl) =>
              // refinement request wins over preliminary,
              // but must still propagate the preliminary immediately
              preliminary(bl2 |*| merge(abstractType(aLbl |*| aReq) |*| b))
            case Right(bLbl) =>
              // preliminary refines the refinement request
              val t1 |*| t2 = split(preliminary(bLbl |*| b))
              returning(
                t1 waitFor labels.neglect(bl2),
                aReq grant t2,
              )
          }
      }
    }

  private def mergePreliminaries(
    merge: (Tp |*| Tp) -⚬ Tp,
  ): (AbsTp.Prelim[Tp] |*| AbsTp.Prelim[Tp]) -⚬ Tp =
    λ { case (aLbl |*| a) |*| (bLbl |*| b) =>
      labels.compare(aLbl |*| bLbl) switch {
        case Left(lbl) =>
          // labels are same
          preliminary(lbl |*| merge(a |*| b))
        case Right(res) =>
          res switch {
            case Left(aLbl) =>
              preliminary(aLbl |*| merge(a |*| b))
            case Right(bLbl) =>
              preliminary(bLbl |*| merge(a |*| b))
          }
      }
    }

  private def mergeConcreteAbstract(
    merge: (Tp |*| Tp) -⚬ Tp,
    split: Tp -⚬ (Tp |*| Tp),
  ): (F[Tp] |*| AbsTp[Tp]) -⚬ Tp =
    λ { case a |*| b =>
      b switch {
        case Left(b) =>
          mergeConcreteAbstractProper(split)(a |*| b)
        case Right(b) =>
          mergeConcreteAbstractPrelim(merge)(a |*| b)
      }
    }

  private def mergeConcreteAbstractProper(
    split: Tp -⚬ (Tp |*| Tp),
  ): (F[Tp] |*| AbsTp.Proper[Tp]) -⚬ Tp =
    λ { case t |*| (lbl |*| req) =>
      val t1 |*| t2 = split(concreteType(t).waitFor(labels.neglect(lbl)))
      returning(
        t1,
        req grant t2,
      )
    }

  private def mergeConcreteAbstractPrelim(
    merge: (Tp |*| Tp) -⚬ Tp,
  ): (F[Tp] |*| AbsTp.Prelim[Tp]) -⚬ Tp =
    // ignore the preliminary placeholder, merge with its follow-up
    λ { case ft |*| (lbl |*| t) =>
      merge(concreteType(ft) |*| t.waitFor(labels.neglect(lbl)))
    }

  private def split_(
    merge: (Tp |*| Tp) -⚬ Tp,
  ): Tp -⚬ (Tp |*| Tp) = rec { self =>
    λ { t =>
      unpack(t) switch {
        case Left(a) =>
          splitAbstract(merge, self)(a)
        case Right(ft) =>
          val ft1 |*| ft2 = F.split(self)(ft)
          concreteType(ft1) |*| concreteType(ft2)
      }
    }
  }

  private def splitAbstract(
    merge: (Tp |*| Tp) -⚬ Tp,
    split: Tp -⚬ (Tp |*| Tp),
  ): AbsTp[Tp] -⚬ (Tp |*| Tp) =
    λ { a =>
      a switch {
        case Left(a)  => splitAbstractProper(merge, split)(a)
        case Right(a) => splitPreliminary(split)(a)
      }
    }

  private def splitPreliminary(
    split: Tp -⚬ (Tp |*| Tp),
  ): AbsTp.Prelim[Tp] -⚬ (Tp |*| Tp) =
    λ { case lbl |*| t =>
      val l1 |*| l2 = labels.split(lbl)
      val t1 |*| t2 = split(t)
      preliminary(l1 |*| t1) |*| preliminary(l2 |*| t2)
    }

  private def splitAbstractProper(
    merge: (Tp |*| Tp) -⚬ Tp,
    split: Tp -⚬ (Tp |*| Tp),
  ): AbsTp.Proper[Tp] -⚬ (Tp |*| Tp) =
    λ { case lbl |*| req =>
      val l1 |*| l2 = labels.split(lbl)
      val t1 |*| resp1 = makeAbstractType(l1)
      val t2 |*| resp2 = makeAbstractType(l2)
      returning(
        t1 |*| t2,
        resp1.toEither switch {
          case Left(t1) =>
            resp2.toEither switch {
              case Left(t2) =>
                req grant merge(t1 |*| t2)
              case Right(req2) =>
                val t11 |*| t12 = split(t1)
                returning(
                  req grant t11,
                  injectL(t12) supplyTo req2,
                )
            }
          case Right(req1) =>
            resp2.toEither switch {
              case Left(t2) =>
                val t21 |*| t22 = split(t2)
                returning(
                  req grant t21,
                  injectL(t22) supplyTo req1,
                )
              case Right(req2) =>
                req.decline switch {
                  case Left(t) =>
                    val t1 |*| t2 = split(t)
                    returning(
                      injectL(t1) supplyTo req1,
                      injectL(t2) supplyTo req2,
                    )
                  case Right(p) =>
                    val p1 |*| p2 = splitTypeParam(p)
                    returning(
                      injectR(p1) supplyTo req1,
                      injectR(p2) supplyTo req2,

                    )
                }
            }
        },
      )
    }

  private def awaitPosFst: (Done |*| Tp) -⚬ Tp =
    rec { self =>
      λ { case d |*| t =>
        unpack(t) switch {
          case Left(a) =>
            a switch {
              case Left(lbl |*| req) => abstractType(lbl.waitFor(d) |*| req)
              case Right(lbl |*| t)  => preliminary(lbl |*| self(d |*| t))
            }
          case Right(ft) =>
            concreteType(F.awaitPosFst(self)(d |*| ft))
        }
      }
    }

  private given Junction.Positive[Tp] =
    Junction.Positive.from(awaitPosFst)

  override def splittable: OutboundType -⚬ SplittableType = id

  override def int: StarterKit.Done -⚬ OutboundType = UnhandledCase.raise("")

  override def tapM: MergeableType -⚬ OutwardType = tap

  override def either: (OutboundType |*| OutboundType) -⚬ OutboundType = UnhandledCase.raise("")

  override def tapS: SplittableType -⚬ OutwardType = tap

  override def eitherOW: (OutwardType |*| OutwardType) -⚬ OutwardType = UnhandledCase.raise("")

  override def recCallOW: (OutwardType |*| OutwardType) -⚬ OutwardType = UnhandledCase.raise("")

  override def pair: (OutboundType |*| OutboundType) -⚬ OutboundType =
    F.pair > concreteType

  override def isRecCall: OutwardType -⚬ (OutwardType |+| (OutwardType |*| OutwardType)) =
    λ { t =>
      TypeOutlet.unpack(t) switch {
        case Left(p) =>
          injectL(TypeOutlet.typeParam(p))
        case Right(ft) =>
          F.isRecCall(ft) switch {
            case Left(ft)       => injectL(TypeOutlet.concreteType(ft))
            case Right(a |*| b) => injectR(a |*| b)
          }
      }
    }

  override def abstractTypeTap: Label -⚬ (Tp |*| Val[Type]) =
    λ { lbl =>
      val l1 |*| l2 = labels.split(lbl)
      val res |*| resp = makeAbstractType(l1)
        res |*| (resp.toEither switch {
          case Left(t) =>
            output(t) waitFor labels.neglect(l2)
          case Right(req) =>
            val p |*| t = typeParamTap(l2)
            returning(t, injectR(p) supplyTo req)
        })
    }

  override def abstractLink: Label -⚬ (Tp |*| Tp) =
    λ { lbl =>
      val l1 |*| l2 = labels.split(lbl)
      val l3 |*| l4 = labels.split(l2)
      val t1 |*| resp = makeAbstractType(l1)
      val nt2 |*| t2 = curry(preliminary)(l3)
      returning(
        t1 |*| t2,
        resp.toEither switch {
          case Left(t) =>
            // TODO: occurs check for `lbl` in `t`
            t.waitFor(labels.neglect(l4)) supplyTo nt2
          case Right(req1) =>
            val l5 |*| l6 = labels.split(l4)
            val t2 |*| resp = makeAbstractType(l5)
            returning(
              resp.toEither switch {
                case Left(t) =>
                  // TODO: occurs check for `lbl` in `t`
                  injectL(t waitFor labels.neglect(l6)) supplyTo req1
                case Right(req2) =>
                  val p1 |*| p2 = typeParamLink(l6)
                  returning(
                    injectR(p1) supplyTo req1,
                    injectR(p2) supplyTo req2,
                  )
              },
              t2 supplyTo nt2,
            )
        },
      )
    }

  override def close: OutboundType -⚬ Done = rec { self =>
    λ { t =>
      unpack(t) switch {
        case Left(a) =>
          a switch {
            case Left(lbl |*| req) =>
              req.decline switch {
                case Left(t)  => join(self(t) |*| labels.neglect(lbl))
                case Right(p) => closeTypeParam(lbl |*| p)
              }
            case Right(lbl |*| t) =>
              join(labels.neglect(lbl) |*| self(t))
          }
        case Right(ft) =>
          F.close(self)(ft)
      }
    }
  }

  override def closeOW: OutwardType -⚬ Done = rec { self =>
    λ { t =>
      dsl.unpack(t) switch {
        case Left(tp)  => closeTypeParam(tp)
        case Right(ft) => F.close(self)(ft)
      }
    }
  }

  override def pairOW: (OutwardType |*| OutwardType) -⚬ OutwardType = UnhandledCase.raise("")

  override def debugPrintGradually: OutboundType -⚬ StarterKit.Done = UnhandledCase.raise("")

  override def label(v: AbstractTypeLabel): One -⚬ Label =
    labels.create(Right(v))

  override def apply1TOW[F[_$4]](F: TypeTag[F]): OutwardType -⚬ OutwardType = UnhandledCase.raise("")

  override def string: StarterKit.Done -⚬ OutboundType = UnhandledCase.raise("")

  override lazy val nested: Nested = {
    val nl = labels.nested

    type NLabel = nl.labels.Label

    type R = -[Tp] |+| Tp |+| (-[Tp] |*| Tp)
    type Q = NLabel =⚬ R

    // val mergeWithAbstractResponse: (Tp |*| (Label |*| Refinement.Response[Tp])) -⚬ R =
    //   λ { case a |*| (bLbl |*| bResp) =>
    //     // The first arg `a` must be scrutinized first, as it may contain
    //     // refinement request corresponding to the second argument,
    //     // in which case the response in the second argument
    //     // will not resolve until request is responded.

    //     unpack(a) switch {
    //       case Left(aLbl |*| aReq) =>
    //         labels.compare(aLbl |*| bLbl) switch {
    //           case Left(lbl) =>
    //             // labels are same
    //             ???
    //           case Right(res) =>
    //             res switch {
    //               case Left(aLbl) =>
    //                 ???
    //               case Right(bLbl) =>
    //                 ???
    //             }
    //         }
    //       case Right(fa) =>
    //         ???
    //     }
    //   }

    // val mergeInOut: (labels.Preliminary |*| -[Tp] |*| Tp) -⚬ R = rec { mergeInOut =>
    //   λ { case p |*| na |*| b =>
    //     val p1 |*| p2 = labels.splitPreliminary(p)
    //     val nt1 |*| t1 = constant(demand[Tp])
    //     returning(
    //       unpack(b) switch {
    //         case Left(b) =>
    //           b switch {
    //             case Left(b) => // abstract type proper
    //               // TODO: must check for presence of `p2` inside `a`
    //               val t1 |*| t2 = split(abstractType(b) waitFor labels.neglectPreliminary(p2))
    //               returning(
    //                 injectL(injectR(t2)),
    //                 t1 supplyTo nt1,
    //               )
    //             case Right(lbl |*| t) => // preliminary type
    //               labels.testEqual(p2 |*| lbl) switch {
    //                 case Left(p) =>
    //                   // same preliminary type; close `t`, propagate the type demand
    //                   val nt2 |*| t1 = λ.closure { (u: $[Tp]) =>
    //                     u.waitFor(join(labels.neglectPreliminary(p) |*| self.close(t)))
    //                   }
    //                   returning(
    //                     injectL(injectL(nt2)),
    //                     t1 supplyTo nt1,
    //                   )
    //                 case Right(p2 |*| lbl) =>
    //                   // different preliminary type
    //                   // TODO: Why is it safe to ignore the preliminary label and wait for the next type?
    //                   mergeInOut(p2.waitFor(labels.neglectPreliminary(lbl)) |*| nt1 |*| t)
    //               }
    //           }
    //         case Right(ft) =>
    //           // TODO: must check for presence of `p2` inside `ft`
    //           val t1 |*| t2 = split(concreteType(ft) waitFor labels.neglectPreliminary(p2))
    //           returning(
    //             injectL(injectR(t2)),
    //             t1 supplyTo nt1,
    //           )
    //       },
    //       preliminary(p1 |*| t1) supplyTo na,
    //     )
    //   }
    // }

    // val mergeQ: (Q |*| Q) -⚬ Q =
    //   λ { case f1 |*| f2 =>
    //     λ.closure { lbl =>
    //       val p0 |*| l = nl.labels.split(lbl)
    //       val l1 |*| l2 = nl.labels.split(l)
    //       val q1 = f1(l1)
    //       val q2 = f2(l2)
    //       val p = nl.preliminary(p0)
    //       q1 switch {
    //         case Left(q1) =>
    //           q1 switch {
    //             case Left(nt1) =>
    //               q2 switch {
    //                 case Left(q2) =>
    //                   q2 switch {
    //                     case Left(nt2) =>
    //                       injectL(injectL(contrapositive(self.split)(factorOutInversion(nt1 |*| nt2))))
    //                     case Right(t2) =>
    //                       mergeInOut(p |*| nt1 |*| t2)
    //                   }
    //                 case Right(nt2 |*| t2) =>
    //                   val nt = contrapositive(self.split)(factorOutInversion(nt1 |*| nt2))
    //                   injectR(nt |*| t2)
    //               }
    //             case Right(t1) =>
    //               q2 switch {
    //                 case Left(q2) =>
    //                   q2 switch {
    //                     case Left(nt2) =>
    //                       mergeInOut(p |*| nt2 |*| t1)
    //                     case Right(t2) =>
    //                       injectL(injectR(self.merge(t1 |*| t2)))
    //                   }
    //                 case Right(nt2 |*| t2) =>
    //                   // val t = self.merge(t1 |*| t2)
    //                   // injectR(nt2 |*| t)
    //                   (p |*| t1 |*| nt2 |*| t2) :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
    //               }
    //           }
    //         case Right(nt1 |*| t1) =>
    //           // q2 switch {
    //           //   case Left(q2) =>
    //           //     q2 switch {
    //           //       case Left(nt2) =>
    //           //         val nt = contrapositive(self.split)(factorOutInversion(nt1 |*| nt2))
    //           //         injectR(nt |*| t1)
    //           //       case Right(t2) =>
    //           //         injectR(nt1 |*| self.merge(t1 |*| t2))
    //           //     }
    //           //   case Right(nt2 |*| t2) =>
    //           //     val nt = contrapositive(self.split)(factorOutInversion(nt1 |*| nt2))
    //           //     val t = self.merge(t1 |*| t2)
    //           //     injectR(nt |*| t)
    //           // }
    //           (p |*| nt1 |*| t1 |*| q2) :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
    //       }
    //     }
    //   }

    def splitQ0: (NLabel |*| NLabel |*| Q) -⚬ (R |*| R) =
      λ { case l1 |*| l2 |*| f =>
        nl.labels.compare(l1 |*| l2) switch {
          case Left(l) =>
            // labels are the same
            f(l) switch {
              case Left(r) =>
                r switch {
                  case Left(nt) =>
                    val nt1 |*| nt2 = contrapositive(self.merge)(nt) :>> distributeInversion
                    injectL(injectL(nt1)) |*| injectL(injectL(nt2))
                  case Right(t) =>
                    val t1 |*| t2 = self.split(t)
                    injectL(injectR(t1)) |*| injectL(injectR(t2))
                }
              case Right(nt |*| t) =>
                // arbitrary split
                injectL(injectL(nt)) |*| injectL(injectR(t))
            }
          case Right(res) =>
            def go: R -⚬ (R |*| R) =
              λ { r =>
                r switch {
                  case Left(r) =>
                    r switch {
                      case Left(nt) =>
                        val nt1 |*| t1 = constant(demand[Tp])
                        val t |*| t2 = self.split(t1)
                        returning(
                          injectL(injectL(nt1)) |*| injectL(injectR(t2)),
                          t supplyTo nt,
                        )
                      case Right(t) =>
                        val t1 |*| t2 = self.split(t)
                        injectL(injectR(t1)) |*| injectL(injectR(t2))
                    }
                  case Right(nt |*| t) =>
                    injectL(injectL(nt)) |*| injectL(injectR(t))
                }
              }
            res switch {
              case Left(l1) =>
                go(f(l1))
              case Right(l2) =>
                go(f(l2)) :>> swap
            }
        }
      }

    val splitQ: Q -⚬ (Q |*| Q) =
      λ { f =>
        val nl1 |*| l1 = constant(demand[NLabel])
        val nl2 |*| l2 = constant(demand[NLabel])
        val r1 |*| r2 = splitQ0(l1 |*| l2 |*| f)
        (nl1 |*| r1) |*| (nl2 |*| r2)
      }

    val qLink: NLabel -⚬ (Q |*| Q) =
      λ { lbl =>
        val nl1 |*| l1 = constant(demand[NLabel])
        val nl2 |*| l2 = constant(demand[NLabel])
        val ntp |*| tp = constant(demand[Tp])
        val tp1 = tp waitFor joinAll(
          nl.labels.neglect(lbl),
          nl.labels.neglect(l1),
          nl.labels.neglect(l2),
        )
        (nl1 |*| injectL(injectL(ntp))) |*| (nl2 |*| injectL(injectR(tp1)))
      }

    val qTap: NLabel -⚬ (Q |*| Val[Type]) =
      λ { case l0 =>
        val res0: $[NLabel =⚬ (R |*| Val[Type])] =
          λ.closure { l1 =>
            val nt |*| t = constant(demand[Tp])
            injectL(injectL(nt)) |*| self.output(t).waitFor(join(nl.labels.neglect(l0) |*| nl.labels.neglect(l1)))
          }
        res0 :>> assocRL
      }

    val outputQ: (NLabel |*| Q) -⚬ Val[Type] = rec { outputQ =>
      λ { case lbl |*| (nLbl |*| q) =>
        val lbl1 |*| lbl2 = nl.labels.split(lbl)
        returning(
          q switch {
            case Left(q) =>
              q switch {
                case Left(nt) =>
                  val l1 |*| l2 = nl.promote(lbl2) :>> labels.split
                  val t |*| resp = makeAbstractType(l1)
                  returning(
                    resp.toEither switch {
                      case Left(t) =>
                        self.output(t)
                          .waitFor(labels.neglect(l2))
                      case Right(req) =>
                        val p |*| res = typeParamTap(l2)
                        returning(
                          res,
                          injectR(p) supplyTo req,
                        )
                    },
                    t supplyTo nt,
                  )
                case Right(t) =>
                  self.output(t)
                    .waitFor(nl.labels.neglect(lbl2))
              }
            case Right(nt |*| t) =>
              (lbl2 |*| nt |*| t) :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
          },
          lbl1 supplyTo nLbl,
        )
      }
    }

    val closeQ: (NLabel |*| Q) -⚬ Done =
      λ { case lbl |*| f =>
        val l1 |*| l2 = nl.labels.split(lbl)
        f(l1) switch {
          case Left(q) =>
            q switch {
              case Left(nt) =>
                val l3 |*| l4 = labels.split(nl.promote(l2))
                val t |*| resp = makeAbstractType(l3)
                returning(
                  resp.close(l4, close),
                  t supplyTo nt,
                )
              case Right(t) =>
                join(close(t) |*| nl.labels.neglect(l2))
            }
          case Right(nt |*| t) =>
            (l2 |*| nt |*| t) :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
        }
      }

    new Nested {
      override val tools: TypeInferencerImpl[F, Q, nl.labels.type] =
        TypeInferencerImpl[F, Q](
          nl.labels,
          F,
          // mergeQ,
          splitQ,
          qLink,
          qTap,
          outputQ,
          closeQ,
        )

      override def lower: tools.TypeOutlet -⚬ Tp = rec { self =>
        λ { t =>
          tools.TypeOutlet.unpack(t) switch {
            case Left(lbl |*| f) =>
              val l1 |*| l2 = tools.labels.split(lbl)
              f(l1) switch {
                case Left(r) =>
                  r switch {
                    case Left(nt) =>
                      val t1 |*| t2 = abstractLink(nl.promote(l2))
                      returning(
                        t1,
                        t2 supplyTo nt,
                      )
                    case Right(t) =>
                      t waitFor nl.labels.neglect(l2)
                  }
                case Right(nt |*| t) =>
                  (l2 |*| nt |*| t) :>> crashNow(s"TODO: eliminate (at ${summon[SourcePos]})")
              }
            case Right(ft) =>
              concreteType(F.map(self)(ft))
          }
        }
      }

      override def plant: InterimType -⚬ (OutboundType |*| OutwardType) =
        UnhandledCase.raise("")

      override def merge: (InterimType |*| InterimType) -⚬ InterimType =
        UnhandledCase.raise("")

      override def mergeLower: (tools.OutwardType |*| tools.OutwardType) -⚬ OutboundType =
        λ { case a |*| b => self.merge(lower(a) |*| lower(b)) }

      override def unnestM: tools.MergeableType -⚬ OutboundType = unnest

      override def mergeZap: (tools.OutwardType |*| tools.OutwardType) -⚬ Val[Type] = UnhandledCase.raise("")

      override def unnestOutward: tools.OutwardType -⚬ OutwardType = UnhandledCase.raise("")

      override def unnestS: tools.SplittableType -⚬ OutboundType = unnest

      override def unnest: tools.OutboundType -⚬ OutboundType =
        tools.tap > lower

    }
  }

  override def tap: OutboundType -⚬ OutwardType = rec { self =>
    λ { t =>
      unpack(t) switch {
        case Left(a) =>
          a switch {
            case Left(lbl |*| req) =>
              import TypeOutlet.given
              req.decline switch {
                case Left(t)  => self(t) waitFor labels.neglect(lbl)
                case Right(p) => TypeOutlet.typeParam(lbl |*| p)
              }
            case Right(lbl |*| t) =>
              self(t waitFor labels.neglect(lbl))
          }
        case Right(ft) =>
          TypeOutlet.concreteType(F.map(self)(ft))
      }
    }
  }

  override def stringOW: StarterKit.Done -⚬ OutwardType = UnhandledCase.raise("")

  override def fixTOW[F[_$2]](F: TypeTag[F]): StarterKit.One -⚬ OutwardType = UnhandledCase.raise("")

  override def recCall: (OutboundType |*| OutboundType) -⚬ OutboundType =
    F.recCall > concreteType

  override def apply1T[F[_$3]](F: TypeTag[F]): OutboundType -⚬ OutboundType = UnhandledCase.raise("")

  override def fixT[F[_$1]](F: TypeTag[F]): StarterKit.One -⚬ OutboundType = UnhandledCase.raise("")

  override def intOW: StarterKit.Done -⚬ OutwardType = UnhandledCase.raise("")

  override def output: Tp -⚬ Val[Type] = rec { self =>
    λ { t =>
      unpack(t) switch {
        case Left(a) => // abstract type
          a switch {
            case Left(label |*| req) => // proper
              req.decline switch {
                case Left(t)  => self(t) waitFor labels.neglect(label)
                case Right(p) => outputTypeParam(label |*| p)
              }
            case Right(label |*| t) => // preliminary
              self(t) waitFor labels.neglect(label)
          }
        case Right(ft) => // concrete type
          F.output(self)(ft)
      }
    }
  }

  override def outputOW: OutwardType -⚬ Val[Type] = rec { self =>
    dsl.unpack > dsl.either(
      outputTypeParam,
      F.output(self),
    )
  }

  override def isPair: OutwardType -⚬ (OutwardType |+| (OutwardType |*| OutwardType)) =
    λ { t =>
      TypeOutlet.unpack(t) switch {
        case Left(p) =>
          injectL(TypeOutlet.typeParam(p))
        case Right(ft) =>
          F.isPair(ft) switch {
            case Left(ft)         => injectL(TypeOutlet.concreteType(ft))
            case Right(t1 |*| t2) => injectR(t1 |*| t2)
          }
      }
    }

  override def mergeable: OutboundType -⚬ MergeableType = id

  object TypeOutlet {
    def pack: ((Label |*| P) |+| F[TypeOutlet]) -⚬ TypeOutlet =
      dsl.pack[[X] =>> (Label |*| P) |+| F[X]]

    def unpack: TypeOutlet -⚬ ((Label |*| P) |+| F[TypeOutlet]) =
      dsl.unpack

    def typeParam: (Label |*| P) -⚬ TypeOutlet =
      injectL > pack

    def concreteType: F[TypeOutlet] -⚬ TypeOutlet =
      injectR > pack

    def awaitPosFst: (Done |*| TypeOutlet) -⚬ TypeOutlet = rec { self =>
      λ { case d |*| t =>
        unpack(t) switch {
          case Left(lbl |*| p) =>
            typeParam(lbl.waitFor(d) |*| p)
          case Right(ft) =>
            concreteType(F.awaitPosFst(self)(d |*| ft))
        }
      }
    }

    given Junction.Positive[TypeOutlet] =
      Junction.Positive.from(awaitPosFst)
  }
}
