package libretto.typology.toylang.typeinfer

import libretto.lambda.util.SourcePos
import libretto.scaletto.StarterKit.*
import libretto.scaletto.StarterKit

trait TypeInferencer {
  type Tp

  def merge: (Tp |*| Tp) -⚬ Tp
  def split: Tp -⚬ (Tp |*| Tp)
}

trait TypeOps[F[_]] {
  def merge[A](f: (A |*| A) -⚬ A): (F[A] |*| F[A]) -⚬ F[A]
}

class TypeInferencerImpl[V, F[_], P](
  val labels: Labels[V],
  F: TypeOps[F],
  unifyTypeParams: (P |*| P) -⚬ One,
) extends TypeInferencer {
  import labels.Label

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
              mergeConcreteAbstract(fb |*| a)
          }
        case Right(fa) =>
          b switch {
            case Left(b) =>
              mergeConcreteAbstract(fa |*| b)
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
                        ???
                    }
                  case Right(p) =>
                    b switch {
                      case Left(b) =>
                        ???
                      case Right(q) =>
                        unifyTypeParams(p |*| q)
                    }
                }
            }
          )
        case Right(res) =>
          def go: (Label |*| Refinement.Request[Tp] |*| Refinement.Request[Tp]) -⚬ Tp =
            ???

          res switch {
            case Left(aLbl) =>
              go(aLbl |*| aReq |*| bReq)
            case Right(bLbl) =>
              go(bLbl |*| bReq |*| aReq)
          }
      }
    }

  private def mergeConcreteAbstract: (F[Tp] |*| AbsTp[Tp]) -⚬ Tp =
    ???

  private def split_(
    merge: (Tp |*| Tp) -⚬ Tp,
  ): Tp -⚬ (Tp |*| Tp) = ???
}
