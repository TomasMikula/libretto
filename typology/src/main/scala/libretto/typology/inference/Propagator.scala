package libretto.typology.inference

import libretto.lambda.util.SourcePos
import libretto.scaletto.StarterKit.*
import scala.annotation.targetName

trait Propagator[F[_], T, V] {
  type Label
  type Tp
  type TypeOutlet

  def Tp: F[Tp] -⚬ Tp = lift

  def lift: F[Tp] -⚬ Tp
  def outlet: F[TypeOutlet] -⚬ TypeOutlet
  def merge: (Tp |*| Tp) -⚬ Tp
  def split: Tp -⚬ (Tp |*| Tp)
  def tap: Tp -⚬ TypeOutlet
  def peek: TypeOutlet -⚬ (F[TypeOutlet] |+| TypeOutlet)
  def write: TypeOutlet -⚬ Val[T]
  def output: Tp -⚬ Val[T] = tap > write
  def close: Tp -⚬ Done

  def label(v: V): One -⚬ Label
  def unwrapLabel: Label -⚬ Val[V]
  def abstractTypeTap: Label -⚬ (Tp |*| Val[T])

  trait Nested {
    val propagator: Propagator[F, T, V]

    def lower: propagator.TypeOutlet -⚬ Tp
    def unnest: propagator.Tp -⚬ Tp
  }

  def nested: Nested

  // TODO: eliminate
  given junctionPositiveTp: Junction.Positive[Tp]
}

object Propagator {

  def instance[F[_], T, V](tparam: V => T)(using TypeOps[F, T, V], Ordering[V]): Propagator[F, T, V] =
    val labels = Labels[V]
    PropagatorImpl[F, T, labels.Label, V](
      labels,
      summon[TypeOps[F, T, V]],
      splitTypeParam = labels.split,
      typeParamLink = labels.split,
      outputTypeParam = labels.unwrapOriginal > mapVal(tparam),
    )
}

private[inference] object PropagatorImpl {
  def apply[F[_], T, P, V](
    labels: Labels[V],
    F: TypeOps[F, T, V],
    splitTypeParam: P -⚬ (P |*| P),
    typeParamLink: labels.Label -⚬ (P |*| P),
    outputTypeParam: P -⚬ Val[T],
  )(using
    Junction.Positive[P],
  ): PropagatorImpl[F, T, P, V, labels.type] =
    new PropagatorImpl(
      labels,
      F,
      splitTypeParam,
      typeParamLink,
      outputTypeParam,
    )
}

private[inference] class PropagatorImpl[
  F[_],
  T,
  P,
  V,
  Lbls <: Labels[V],
](
  val labels: Lbls,
  F: TypeOps[F, T, V],
  splitTypeParam: P -⚬ (P |*| P),
  typeParamLink: labels.Label -⚬ (P |*| P),
  outputTypeParam: P -⚬ Val[T],
)(using
  Junction.Positive[P],
) extends Propagator[F, T, V] { self =>

  override type Label = labels.Label
  override type TypeOutlet = Rec[[X] =>> P |+| F[X]]

  object Refinement {
    opaque type Request[T] = -[Response[T]]
    opaque type Response[T] = T |+| -[TypeOutlet]

    def makeRequest[T]: One -⚬ (Request[T] |*| Response[T]) =
      forevert

    extension [T](req: $[Request[T]]) {
      def grant(t: $[T])(using SourcePos, LambdaContext): $[One] =
        injectL(t) supplyTo req

      def decline(using SourcePos, LambdaContext): $[TypeOutlet] =
        die(req contramap injectR)

      @targetName("closeRefinementRequest")
      def close(using SourcePos, LambdaContext): $[Done] =
        TypeOutlet.close(req.decline)
    }

    extension [T](resp: $[Response[T]])
      def toEither: $[T |+| -[TypeOutlet]] =
        resp

      def mapWith[X, U](f: (X |*| T) -⚬ U)(x: $[X])(using SourcePos, LambdaContext)(using X: Closeable[X]): $[Response[U]] =
        import TypeOutlet.given
        given Junction.Positive[-[TypeOutlet]] = Junction.Positive.insideInversion[TypeOutlet]
        resp either {
          case Left(t)  => injectL(f(x |*| t))
          case Right(t) => injectR(t waitFor X.close(x))
        }
  }

  object AbsTp {
    type Proper[T] = Label |*| Refinement.Request[T]
    type Prelim[T] = Label |*| T
  }
  type AbsTp[T] = AbsTp.Proper[T] |+| AbsTp.Prelim[T]

  override type Tp = Rec[[Tp] =>> AbsTp[Tp] |+| F[Tp]]

  private def pack: (AbsTp[Tp] |+| F[Tp]) -⚬ Tp =
    dsl.pack[[X] =>> AbsTp[X] |+| F[X]]

  private def unpack: Tp -⚬ (AbsTp[Tp] |+| F[Tp]) =
    dsl.unpack[[X] =>> AbsTp[X] |+| F[X]]

  private def abstType: (Label |*| Refinement.Request[Tp]) -⚬ Tp =
    injectL > injectL > pack

  private def preliminary: (Label |*| Tp) -⚬ Tp =
    injectR > injectL > pack

  private def concreteType: F[Tp] -⚬ Tp =
    injectR > pack

  override val lift: F[Tp] -⚬ Tp =
    concreteType

  override val outlet: F[TypeOutlet] -⚬ TypeOutlet =
    TypeOutlet.concreteType

  def makeAbstractType: Label -⚬ (Tp |*| Refinement.Response[Tp]) =
    λ { case +(lbl) =>
      val req |*| resp = constant(Refinement.makeRequest[Tp])
      abstType(lbl |*| req) |*| resp.mapWith(occursCheck)(lbl)
    }

  private def occursCheck: (Label |*| Tp) -⚬ Tp = rec { self =>
    λ { case lbl0 |*| t =>
      unpack(t) either {
        case Left(absTp) =>
          absTp either {
            case Left(lbl |*| req) =>
              labels.testEqual(lbl0 |*| lbl) either {
                case Left(l) => // forbidden label found
                  val +(v) = labels.unwrapOriginal(l)
                  val t1 = concreteType(F.forbiddenSelfReference(v))
                  val t2 = concreteType(F.forbiddenSelfReference(v))
                  returning(t1, req grant t2)
                case Right(lbl0 |*| lbl) =>
                  abstType(lbl.waitFor(labels.neglect(lbl0)) |*| req)
              }
            case Right(lbl |*| t) => // preliminary
              labels.testEqual(lbl0 |*| lbl) either {
                case Left(l) => // forbidden label found
                  returning(
                    concreteType(F.forbiddenSelfReference(labels.unwrapOriginal(l))),
                    hackyDiscard(close(t)),
                  )
                case Right(lbl0 |*| lbl) =>
                  preliminary(lbl |*| self(lbl0 |*| t))
              }
          }
        case Right(ft) =>
          concreteType(F.mapWith(self)(lbl0 |*| ft))
      }
    }
  }

  override lazy val merge: (Tp |*| Tp) -⚬ Tp =
    rec { self =>
      merge_(split_(self))
    }

  override lazy val split: Tp -⚬ (Tp |*| Tp) =
    rec { self =>
      split_(merge_(self))
    }

  private def merge_(
    split: Tp -⚬ (Tp |*| Tp),
  ): (Tp |*| Tp) -⚬ Tp = rec { self =>
    par(unpack, unpack) > λ { case a |*| b =>
      a either {
        case Left(a) =>
          b either {
            case Left(b) =>
              mergeAbstractTypes(self, split)(a |*| b)
            case Right(fb) =>
              mergeConcreteAbstract(self, split)(fb |*| a)
          }
        case Right(fa) =>
          b either {
            case Left(b) =>
              mergeConcreteAbstract(self, split)(fa |*| b)
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
    λ { case a |*| b =>
      a either {
        case Left(a) =>
          b either {
            case Left(b) =>
              mergeAbstractTypesProper(merge, split)(a |*| b)
            case Right(b) =>
              mergeAbstractProperPreliminary(merge, split)(a |*| b)
          }
        case Right(a) =>
          b either {
            case Left(b) =>
              mergeAbstractProperPreliminary(merge, split)(b |*| a)
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
      labels.compare(aLbl |*| bLbl) either {
        case Left(lbl) =>
          // Labels are same, i.e. both refer to the same type.
          // Propagate one (arbitrary) of them, close the other.
          returning(
            abstType(lbl |*| aReq),
            hackyDiscard(bReq.close),
          )

        case Right(res) =>
          def go: (AbsTp.Proper[Tp] |*| Refinement.Request[Tp]) -⚬ Tp =
            λ { case absTp |*| bReq =>
              val t1 |*| t2 = splitAbstractProper(merge, split)(absTp)
              returning(t1, bReq grant t2)
            }

          res either {
            case Left(aLbl)  => go(aLbl |*| aReq |*| bReq)
            case Right(bLbl) => go(bLbl |*| bReq |*| aReq)
          }
      }
    }

  private def mergeAbstractProperPreliminary(
    merge: (Tp |*| Tp) -⚬ Tp,
    split: Tp -⚬ (Tp |*| Tp),
  ): (AbsTp.Proper[Tp] |*| AbsTp.Prelim[Tp]) -⚬ Tp =
    λ { case (aLbl |*| aReq) |*| (bLbl |*| b) =>
      // (labels.alsoShow(aLbl) |*| labels.alsoShow(bLbl)) match { case (aLbl |*| as) |*| (bLbl |*| bs) =>
      val bl1 |*| bl2 = labels.split(bLbl)
      // returning(
      labels.compare(aLbl |*| bl1) either {
        case Left(lbl) =>
          // Labels are equal, refer to the same type.
          // Close the refinement request, propagate the preliminary.
          returning(
            preliminary(bl2.waitFor(labels.neglect(lbl)) |*| b),
            hackyDiscard(aReq.close),
          )
        case Right(res) =>
          res either {
            case Left(aLbl) =>
              // refinement request wins over preliminary,
              // but must still propagate the preliminary immediately
              preliminary(bl2 |*| merge(abstType(aLbl |*| aReq) |*| b))
            case Right(bLbl) =>
              // preliminary refines the refinement request
              val t1 |*| t2 = split(preliminary(bLbl |*| b))
              returning(
                t1 waitFor labels.neglect(bl2),
                aReq grant t2,
              )
          }
      }
      // ,(as ** bs) :>> printLine { case (as, bs) => s"Merging PROPER $as and PRELIMINARY $bs" } :>> hackyDiscard,
      // )
      // }
    }

  private def mergePreliminaries(
    merge: (Tp |*| Tp) -⚬ Tp,
  ): (AbsTp.Prelim[Tp] |*| AbsTp.Prelim[Tp]) -⚬ Tp =
    λ { case (aLbl |*| a) |*| (bLbl |*| b) =>
      // (labels.alsoShow(aLbl) |*| labels.alsoShow(bLbl)) match { case (aLbl |*| as) |*| (bLbl |*| bs) =>
      // returning(
      labels.compare(aLbl |*| bLbl) either {
        case Left(lbl) =>
          // labels are same
          preliminary(lbl |*| merge(a |*| b))
        case Right(res) =>
          res either {
            case Left(aLbl) =>
              val al1 |*| al2 = labels.split(aLbl)
              val a1 = preliminary(al1 |*| a) // winner (`a`) must keep checking for its own label in the loser (`b`)
              preliminary(al2 |*| merge(a1 |*| b))
            case Right(bLbl) =>
              val bl1 |*| bl2 = labels.split(bLbl)
              val b1 = preliminary(bl1 |*| b) // winner (`b`) must keep checking for its own label in the loser (`a`)
              preliminary(bl2 |*| merge(a |*| b1))
          }
      }
      // ,(as ** bs) :>> printLine { case (as, bs) => s"Merging PRELIMINARIES $as and $bs" } :>> hackyDiscard,
      // )
      // }
    }

  private def mergeConcreteAbstract(
    merge: (Tp |*| Tp) -⚬ Tp,
    split: Tp -⚬ (Tp |*| Tp),
  ): (F[Tp] |*| AbsTp[Tp]) -⚬ Tp =
    λ { case a |*| b =>
      b either {
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
    λ { case ft |*| (lbl |*| t) =>
      preliminary(lbl |*| merge(concreteType(ft) |*| t))
    }

  private def split_(
    merge: (Tp |*| Tp) -⚬ Tp,
  ): Tp -⚬ (Tp |*| Tp) = rec { self =>
    λ { t =>
      unpack(t) either {
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
      a either {
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
        resp1.toEither either {
          case Left(t1) =>
            resp2.toEither either {
              case Left(t2) =>
                req grant merge(t1 |*| t2)
              case Right(req2) =>
                val t11 |*| t12 = split(t1)
                returning(
                  req grant t11,
                  tap(t12) supplyTo req2,
                )
            }
          case Right(req1) =>
            resp2.toEither either {
              case Left(t2) =>
                val t21 |*| t22 = split(t2)
                returning(
                  req grant t21,
                  tap(t22) supplyTo req1,
                )
              case Right(req2) =>
                val t1 |*| t2 = TypeOutlet.split(req.decline)
                returning(
                  t1 supplyTo req1,
                  t2 supplyTo req2,
                )
            }
        },
      )
    }

  private def awaitPosFst: (Done |*| Tp) -⚬ Tp =
    rec { self =>
      λ { case d |*| t =>
        unpack(t) either {
          case Left(a) =>
            a either {
              case Left(lbl |*| req) => abstType(lbl.waitFor(d) |*| req)
              case Right(lbl |*| t)  => preliminary(lbl |*| self(d |*| t))
            }
          case Right(ft) =>
            concreteType(F.awaitPosFst(self)(d |*| ft))
        }
      }
    }

  override given junctionPositiveTp: Junction.Positive[Tp] =
    Junction.Positive.from(awaitPosFst)

  override lazy val abstractTypeTap: Label -⚬ (Tp |*| Val[T]) =
    λ { lbl =>
      val l1 |*| l2 = labels.split(lbl)
      val res |*| resp = makeAbstractType(l1)
        res |*| (resp.toEither either {
          case Left(t) =>
            output(t) waitFor labels.neglect(l2)
          case Right(req) =>
            val p1 |*| p2 = typeParamLink(l2)
            val t = outputTypeParam(p1)
            returning(t, TypeOutlet.typeParam(p2) supplyTo req)
        })
    }

  private def abstractLink: Label -⚬ (Tp |*| Tp) =
    λ { lbl =>
      // val lbl1 = labels.alsoDebugPrint(s => s"Creating link for $s")(lbl)
      val l1 |*| l2 = labels.split(lbl)
      val l3 |*| l4 = labels.split(l2)
      val t1 |*| resp = makeAbstractType(l1)
      val nt2 |*| t2 = curry(preliminary)(l3)
      returning(
        t1 |*| t2,
        resp.toEither either {
          case Left(t) =>
            // TODO: occurs check for `lbl` in `t`
            val l4_ = l4 //:>> labels.alsoDebugPrint(s => s"Link-req of $s returned as REFINED")
            t.waitFor(labels.neglect(l4_)) supplyTo nt2
          case Right(req1) =>
            val l4_ = l4 //:>> labels.alsoDebugPrint(s => s"Link-req of $s returned as DECLINED. Sending opposite request.")
            val l5 |*| l6 = labels.split(l4_)
            val t2 |*| resp = makeAbstractType(l5)
            returning(
              resp.toEither either {
                case Left(t) =>
                  // TODO: occurs check for `lbl` in `t`
                  val l6_ = l6 //:>> labels.alsoDebugPrint(s => s"Op-req of $s returned as REFINED")
                  tap(t waitFor labels.neglect(l6_)) supplyTo req1
                case Right(req2) =>
                  val l6_ = l6 //:>> labels.alsoDebugPrint(s => s"Op-req of $s returned as DECLINED")
                  val p1 |*| p2 = typeParamLink(l6_)
                  returning(
                    TypeOutlet.typeParam(p1) supplyTo req1,
                    TypeOutlet.typeParam(p2) supplyTo req2,
                  )
              },
              t2 supplyTo nt2,
            )
        },
      )
    }

  override val close: Tp -⚬ Done = rec { self =>
    λ { t =>
      unpack(t) either {
        case Left(a) =>
          a either {
            case Left(lbl |*| req) =>
              joinAll(
                TypeOutlet.close(req.decline),
                labels.neglect(lbl),
              )
            case Right(lbl |*| t) =>
              join(labels.neglect(lbl) |*| self(t))
          }
        case Right(ft) =>
          F.close(self)(ft)
      }
    }
  }

  override def label(v: V): One -⚬ Label =
    labels.create(v)

  override def unwrapLabel: Label -⚬ Val[V] =
    labels.unwrapOriginal

  override lazy val nested: Nested = {
    val nl = labels.nested

    type NLabel  = nl.labels.Label

    type Q = NLabel |*| (-[Tp] |+| Tp)

    val splitQ: Q -⚬ (Q |*| Q) =
      λ { case lbl |*| q =>
        val l1 |*| l2 = nl.labels.split(lbl)
        val q1 |*| q2 = q either {
          case Left(nt) =>
            val nt1 |*| nt2 = contrapositive(self.merge)(nt) :>> distributeInversion
            injectL(nt1) |*| injectL(nt2)
          case Right(t) =>
            val t1 |*| t2 = self.split(t)
            injectR(t1) |*| injectR(t2)
        }
        (l1 |*| q1) |*| (l2 |*| q2)
      }

    val qLink: NLabel -⚬ (Q |*| Q) =
      λ { lbl =>
        val ntp |*| tp = constant(demand[Tp])
        val l1 |*| l2 = nl.labels.split(lbl)
        (l1 |*| injectL(ntp)) |*| (l2 |*| injectR(tp))
      }

    val outputQ: Q -⚬ Val[T] =
      λ { case lbl |*| q =>
        q either {
          case Left(nt) =>
            val t |*| t0 = abstractTypeTap(nl.lower(lbl))
            returning(t0, t supplyTo nt)
          case Right(t) =>
            self.output(t)
              .waitFor(nl.labels.neglect(lbl))
        }
      }

    new Nested {
      override val propagator: PropagatorImpl[F, T, Q, V, nl.labels.type] =
        PropagatorImpl[F, T, Q, V](
          nl.labels,
          F,
          splitQ,
          qLink,
          outputQ,
        )(using
          Junction.Positive.byFst,
        )

      override val lower: propagator.TypeOutlet -⚬ Tp = rec { self =>
        λ { t =>
          propagator.TypeOutlet.unpack(t) either {
            case Left(lbl |*| q) =>
              q either {
                case Left(nt) =>
                  val t1 |*| t2 = abstractLink(nl.lower(lbl))
                  returning(
                    t1,
                    t2 supplyTo nt,
                  )
                case Right(t) =>
                  t waitFor nl.labels.neglect(lbl)
              }
            case Right(ft) =>
              concreteType(F.map(self)(ft))
          }
        }
      }

      override def unnest: propagator.Tp -⚬ Tp =
        propagator.tap > lower
    }
  }

  override val tap: Tp -⚬ TypeOutlet = rec { self =>
    λ { t =>
      unpack(t) either {
        case Left(a) =>
          a either {
            case Left(lbl |*| req) =>
              import TypeOutlet.given
              req.decline waitFor labels.neglect(lbl)
            case Right(lbl |*| t) =>
              self(t waitFor labels.neglect(lbl))
          }
        case Right(ft) =>
          TypeOutlet.concreteType(F.map(self)(ft))
      }
    }
  }

  override val peek: TypeOutlet -⚬ (F[TypeOutlet] |+| TypeOutlet) =
    λ { t =>
      TypeOutlet.unpack(t) either {
        case Left(p)   => injectR(TypeOutlet.typeParam(p))
        case Right(ft) => injectL(ft)
      }
    }

  override val write: TypeOutlet -⚬ Val[T] = rec { self =>
    dsl.unpack > dsl.either(
      outputTypeParam,
      F.output(self),
    )
  }

  object TypeOutlet {
    private val pack: (P |+| F[TypeOutlet]) -⚬ TypeOutlet =
      dsl.pack[[X] =>> P |+| F[X]]

    val unpack: TypeOutlet -⚬ (P |+| F[TypeOutlet]) =
      dsl.unpack

    val typeParam: P -⚬ TypeOutlet =
      injectL > pack

    val concreteType: F[TypeOutlet] -⚬ TypeOutlet =
      injectR > pack

    val split: TypeOutlet -⚬ (TypeOutlet |*| TypeOutlet) =
      rec { self =>
        λ { t =>
          unpack(t) either {
            case Left(p) =>
              val p1 |*| p2 = splitTypeParam(p)
              typeParam(p1) |*| typeParam(p2)
            case Right(ft) =>
              val ft1 |*| ft2 = F.split(self)(ft)
              concreteType(ft1) |*| concreteType(ft2)
          }
        }
      }

    val close: TypeOutlet -⚬ Done =
      rec { self =>
        unpack > either(outputTypeParam > neglect, F.close(self))
      }

    val awaitPosFst: (Done |*| TypeOutlet) -⚬ TypeOutlet = rec { self =>
      λ { case d |*| t =>
        unpack(t) either {
          case Left(p) =>
            typeParam(p waitFor d)
          case Right(ft) =>
            concreteType(F.awaitPosFst(self)(d |*| ft))
        }
      }
    }

    given Junction.Positive[TypeOutlet] =
      Junction.Positive.from(awaitPosFst)
  }
}
