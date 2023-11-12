package libretto.typology.toylang.typeinfer

import libretto.lambda.util.SourcePos
import libretto.scaletto.StarterKit.*
import libretto.scaletto.StarterKit
import libretto.typology.toylang.terms.TypedFun.Type
import libretto.typology.toylang.types.TypeTag
import libretto.typology.toylang.types.{AbstractTypeLabel, ScalaTypeParam}
import libretto.typology.toylang.typeinfer.Tools.ToolsImpl.NonAbstractTypeF
// import libretto.typology.toylang.types.{AbstractTypeLabel, ScalaTypeParam, TypeAlgebra, TypeTag}

trait TypeInferencer extends Tools {
  type Tp


  override type OutboundType = Tp
  override type OutwardType = Tp
  override type MergeableType = Tp
  override type SplittableType = Tp

  def merge: (Tp |*| Tp) -⚬ Tp
  def split: Tp -⚬ (Tp |*| Tp)
}

trait TypeOps[F[_]] {
  def merge[A](f: (A |*| A) -⚬ A): (F[A] |*| F[A]) -⚬ F[A]
  def output[A](f: A -⚬ Val[Type]): F[A] -⚬ Val[Type]
}

object TypeInferencer {
  private type V = Either[ScalaTypeParam, AbstractTypeLabel]

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

  val labels = new Labels[Either[ScalaTypeParam, AbstractTypeLabel]]

  val typeOps: TypeOps[Tools.ToolsImpl.NonAbstractTypeF] =
    new TypeOps[Tools.ToolsImpl.NonAbstractTypeF] {
      override def merge[A](f: (A |*| A) -⚬ A): (NonAbstractTypeF[A] |*| NonAbstractTypeF[A]) -⚬ NonAbstractTypeF[A] =
        Tools.ToolsImpl.NonAbstractType.merge(f, ???)

      override def output[A](f: A -⚬ Val[Type]): NonAbstractTypeF[A] -⚬ Val[Type] =
        Tools.ToolsImpl.NonAbstractType.output(f)
    }

  def instance: TypeInferencer =
    TypeInferencerImpl[V, Tools.ToolsImpl.NonAbstractTypeF, Done](
      labels,
      typeOps,
      mergeTypeParams = join,
      splitTypeParam = fork,
      typeParamTap = labels.unwrapOriginal > mapVal(x => Type.abstractType(x)) > signalPosFst,
      outputTypeParam = fst(labels.unwrapOriginal > mapVal(x => Type.abstractType(x))) > awaitPosSnd,
    )
}

class TypeInferencerImpl[V, F[_], P](
  val labels: Labels[V],
  F: TypeOps[F],
  mergeTypeParams: (P |*| P) -⚬ P,
  splitTypeParam: P -⚬ (P |*| P),
  typeParamTap: labels.Label -⚬ (P |*| Val[Type]),
  outputTypeParam: (labels.Label |*| P) -⚬ Val[Type],
) extends TypeInferencer { self =>

  override type Label = labels.Label

  type AbsTp[T] = Label |*| Refinement.Request[T]

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
    }

    extension [T](resp: $[Response[T]]) {
      def toEither: $[T |+| -[T |+| P]] =
        resp
    }
  }

  override type Tp = Rec[[Tp] =>> AbsTp[Tp] |+| F[Tp]]

  private def pack: (AbsTp[Tp] |+| F[Tp]) -⚬ Tp =
    dsl.pack[[X] =>> AbsTp[X] |+| F[X]]

  private def unpack: Tp -⚬ (AbsTp[Tp] |+| F[Tp]) =
    dsl.unpack[[X] =>> AbsTp[X] |+| F[X]]

  def abstractType: AbsTp[Tp] -⚬ Tp =
    injectL > pack

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
              mergeConcreteAbstract(split)(fb |*| a)
          }
        case Right(fa) =>
          b switch {
            case Left(b) =>
              mergeConcreteAbstract(split)(fa |*| b)
            case Right(fb) =>
              concreteType(F.merge(self)(fa |*| fb))
          }
      }
    }
  }

  private def mergeAbstractTypes(
    merge: (Tp |*| Tp) -⚬ Tp,
    split: Tp -⚬ (Tp |*| Tp),
  ): (AbsTp[Tp] |*| AbsTp[Tp]) -⚬ Tp =
    λ { case (aLbl |*| aReq) |*| (bLbl |*| bReq) =>
      labels.compare(aLbl |*| bLbl) switch {
        case Left(lbl) =>
          // labels are same => neither refines the other
          val res |*| resp = makeAbstractType(lbl)
          returning(
            res,
            resp.toEither switch {
              case Left(t) =>
                val t1 |*| t2 = split(t)
                returning(
                  aReq grant t1,
                  bReq grant t2,
                )
              case Right(req) =>
                val a = aReq.decline
                val b = bReq.decline
                a switch {
                  case Left(a) =>
                    b switch {
                      case Left(b) =>
                        injectL(merge(a |*| b)) supplyTo req
                      case Right(q) =>
                        (a |*| q |*| req) :>> crashNow(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
                    }
                  case Right(p) =>
                    b switch {
                      case Left(b) =>
                        (p |*| b |*| req) :>> crashNow(s"The same abstract type resolved to two different outcomes (at ${summon[SourcePos]})")
                      case Right(q) =>
                        injectR(mergeTypeParams(p |*| q)) supplyTo req
                    }
                }
            }
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

  private def mergeConcreteAbstract(
    split: Tp -⚬ (Tp |*| Tp),
  ): (F[Tp] |*| AbsTp[Tp]) -⚬ Tp =
    λ { case t |*| (lbl |*| req) =>
      val t1 |*| t2 = split(concreteType(t))
      returning(
        t1,
        req grant t2,
      )
    }

  private def split_(
    merge: (Tp |*| Tp) -⚬ Tp,
  ): Tp -⚬ (Tp |*| Tp) = ???

  override def splittable: OutboundType -⚬ SplittableType = id

  override def closeOW: OutwardType -⚬ StarterKit.Done = ???

  override def int: StarterKit.Done -⚬ OutboundType = ???

  override def tapM: MergeableType -⚬ OutwardType = ???

  override def either: (OutboundType |*| OutboundType) -⚬ OutboundType = ???

  override def tapS: SplittableType -⚬ OutwardType = ???

  override def eitherOW: (OutwardType |*| OutwardType) -⚬ OutwardType = ???

  override def recCallOW: (OutwardType |*| OutwardType) -⚬ OutwardType = ???

  override def pair: (OutboundType |*| OutboundType) -⚬ OutboundType = ???

  override def isRecCall: OutwardType -⚬ (OutwardType |+| (OutwardType |*| OutwardType)) = ???

  override def abstractTypeTap: Label -⚬ (Tp |*| Val[Type]) =
    λ { lbl =>
      val l1 |*| l2 = labels.split(lbl)
      val res |*| resp =  makeAbstractType(l1)
        res |*| (resp.toEither switch {
          case Left(t) =>
            output(t) waitFor labels.neglect(l2)
          case Right(req) =>
            val p |*| t = typeParamTap(l2)
            returning(t, injectR(p) supplyTo req)
        })
    }

  override def close: OutboundType -⚬ StarterKit.Done = ???

  override def pairOW: (OutwardType |*| OutwardType) -⚬ OutwardType = ???

  override def debugPrintGradually: OutboundType -⚬ StarterKit.Done = ???

  override def label(v: AbstractTypeLabel): StarterKit.One -⚬ Label = ???

  override def apply1TOW[F[_$4]](F: TypeTag[F]): OutwardType -⚬ OutwardType = ???

  override def string: StarterKit.Done -⚬ OutboundType = ???

  override lazy val nested: Nested =
    new Nested {
      override val tools: self.type = self

      override def mergeLower: (tools.OutwardType |*| tools.OutwardType) -⚬ OutboundType = self.merge
      override def unnestM: tools.MergeableType -⚬ OutboundType = ???

      override def mergeZap: (OutwardType |*| OutwardType) -⚬ StarterKit.dsl.Val[Type] = ???

      override def unnestOutward: OutwardType -⚬ OutwardType = ???

      override def unnestS: tools.SplittableType -⚬ OutboundType = ???

      override def unnest: OutboundType -⚬ OutboundType = ???

    }

  override def tap: OutboundType -⚬ OutwardType = ???

  override def stringOW: StarterKit.Done -⚬ OutwardType = ???

  override def fixTOW[F[_$2]](F: TypeTag[F]): StarterKit.One -⚬ OutwardType = ???

  override def recCall: (OutboundType |*| OutboundType) -⚬ OutboundType = ???

  override def apply1T[F[_$3]](F: TypeTag[F]): OutboundType -⚬ OutboundType = ???

  override def fixT[F[_$1]](F: TypeTag[F]): StarterKit.One -⚬ OutboundType = ???

  override def intOW: StarterKit.Done -⚬ OutwardType = ???

  override def output: Tp -⚬ Val[Type] = rec { self =>
    unpack > dsl.either(
      λ { case label |*| req => // abstract type
        req.decline switch {
          case Left(t)  => self(t) waitFor labels.neglect(label)
          case Right(p) => outputTypeParam(label |*| p)
        }
      },
      F.output(self),
    )
  }

  // def output[T, Y, X](
  //   outputX: X -⚬ Val[Type],
  //   outputNegT: (TParamLabel |*| -[T]) -⚬ Val[Type],
  // ): TypeSkelet[T, Y, X] -⚬ Val[Type] =

  override def isPair: OutwardType -⚬ (OutwardType |+| (OutwardType |*| OutwardType)) = ???

  override def outputOW: OutwardType -⚬ StarterKit.dsl.Val[Type] = ???

  override def mergeable: OutboundType -⚬ MergeableType = ???
}
