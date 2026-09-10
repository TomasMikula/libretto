package libretto.lambda

import libretto.lambda.util.{Exists, TypeEq}
import libretto.lambda.util.Exists.Indeed
import libretto.lambda.util.TypeEq.Refl

/** A semigroupal category on a subset of Scala types (narrow), where the monoidal product (tensor)
  * is not given as a fixed binary type constructor, but is *witnessed* (hence "W" in WSemigroupal)
  * by a ternary relation `Prd[A, B, P]` that `P` is the tensor of `A` and `B`.
  *
  * @tparam Obj  witnesses that a Scala type is an object of the category.
  * @tparam ->   morphism of the category
  * @tparam Prd  witnesses tensor formation: `Prd[A, B, P]` means that `P` is the tensor of `A` and `B`.
  */
trait NarrowWSemigroupalCategory[Obj[_], ->[_, _], Prd[_, _, _]]
  extends NarrowCategory[Obj, ->]
{
  import NarrowWSemigroupalCategory.*

  /** Witnesses that `As`` is an intensional description of an n-ary product with denotation `P`. */
  sealed trait PrdN[As, P] {
    infix def uniq[Q](that: PrdN[As, Q]): P =:= Q

    def ×[Bs, Q](that: PrdN[Bs, Q]): Exists[[R] =>> (PrdN[As × Bs, R], Prd[P, Q, R])] =
      wtensor(prdNObj(this), prdNObj(that)) match
        case Indeed(r) => Indeed((PrdN(r)(this, that), r))
  }

  object PrdN {
    case class Atom[A](a: Obj[A]) extends PrdN[\[A], A] {
      override def uniq[Q](that: PrdN[\[A], Q]): A =:= Q =
        that match
          case Atom(_) => summon
    }

    case class Op[As, A, Bs, B, P](
      l: PrdN[As, A],
      r: PrdN[Bs, B],
      op: Prd[A, B, P]
    ) extends PrdN[As × Bs, P] {
      override def uniq[Q](that: PrdN[As × Bs, Q]): P =:= Q =
        that match
          case Op(l1, r1, op1) =>
            (l uniq l1, r uniq r1) match
              case (TypeEq(Refl()), TypeEq(Refl())) => tensorUniq(op, op1)
    }

    /** Witnesses that type `A` formally describes the intent of forming an n-ary product. */
    type Intension[A] = PrdN[A, ?]

    given [A, B] => (a: Intension[A], b: Intension[B]) => Intension[A × B] =
      wtensor(prdNObj(a), prdNObj(b)) match
        case Indeed(p) => PrdN(p)(a, b)

    def atom[A](using a: Obj[A]): PrdN[\[A], A] =
      Atom(a)

    def lift[A, B, P](p: Prd[A, B, P])(using Obj[A], Obj[B]): PrdN[\[A] × \[B], P] =
      Op(atom[A], atom[B], p)

    def apply[A, B, P](p: Prd[A, B, P])[As, Bs](as: PrdN[As, A], bs: PrdN[Bs, B]): PrdN[As × Bs, P] =
      Op(as, bs, p)
  }

  /** Auxiliary arrow to operate on intensional descriptions of products. */
  sealed trait -×>[As, Bs] {
    type Src
    type Tgt

    def underlying: Src -> Tgt
    def src: PrdN[As, Src]
    def tgt: PrdN[Bs, Tgt]

    def extract[A, B](a: PrdN[As, A], b: PrdN[Bs, B]): A -> B
    def >[Cs](that: Bs -×> Cs): As -×> Cs
  }

  object -×> {
    case class Impl[As, Bs, P, Q](
      p: PrdN[As, P],
      q: PrdN[Bs, Q],
      f: P -> Q,
    ) extends (As -×> Bs) {
      override type Src = P
      override type Tgt = Q

      override def underlying: Src -> Tgt = f
      override def src: PrdN[As, P] = p
      override def tgt: PrdN[Bs, Q] = q

      override def extract[A, B](a: PrdN[As, A], b: PrdN[Bs, B]): A -> B =
        (p uniq a, q uniq b) match
          case (TypeEq(Refl()), TypeEq(Refl())) => f

      override def >[Cs](that: Bs -×> Cs): As -×> Cs =
        that match
          case Impl(q1, r, g) =>
            (q uniq q1) match
              case TypeEq(Refl()) => Impl(p, r, f > g)
    }

    def apply[As, Bs, P, Q](
      p: PrdN[As, P],
      q: PrdN[Bs, Q],
    )(
      f: P -> Q,
    ): (As -×> Bs) =
      Impl(p, q, f)

    def lift[A: Obj, B: Obj](f: A -> B): \[A] -×> \[B] =
      Impl(PrdN.atom[A], PrdN.atom[B], f)
  }

  def wtensor[A, B](
    wa: Obj[A],
    wb: Obj[B],
  ): Exists[[P] =>> Prd[A, B, P]]

  def tensorObj[A: Obj, B: Obj, P](p: Prd[A, B, P]): Obj[P]

  def prdNObj[As, P](p: PrdN[As, P]): Obj[P] =
    p match
      case PrdN.Atom(a) => a
      case PrdN.Op(a, b, p) => tensorObj(p)(using prdNObj(a), prdNObj(b))

  given [As, P] => (p: PrdN[As, P]) => Obj[P] =
    prdNObj(p)

  extension [As, P](p: PrdN[As, P])
    def obj: Obj[P] = prdNObj(p)

  private def iid_[As, P](w: PrdN[As, P]): As -×> As =
    -×>(w, w)(id[P](using prdNObj(w)))

  def iid[As](using as: PrdN.Intension[As]): As -×> As =
    iid_(as)

  def ipar[A1, A2, B1, B2](
    f1: A1 -×> B1,
    f2: A2 -×> B2,
  ): (A1 × A2) -×> (B1 × B2)

  def wpar[A1, A2, B1, B2](
    f1: A1 -> B1,
    f2: A2 -> B2,
  )(using
    a1: Obj[A1], a2: Obj[A2],
    b1: Obj[B1], b2: Obj[B2],
  )[P, Q](
    pSrc: Prd[A1, A2, P],
    pTgt: Prd[B1, B2, Q],
  ): P -> Q =
    ipar(-×>.lift(f1), -×>.lift(f2))
      .extract(PrdN.lift(pSrc), PrdN.lift(pTgt))

  def iassocLR[A, B, C](using a: PrdN.Intension[A], b: PrdN.Intension[B], c: PrdN.Intension[C]): ((A × B) × C) -×> (A × (B × C))
  def iassocRL[A, B, C](using a: PrdN.Intension[A], b: PrdN.Intension[B], c: PrdN.Intension[C]): (A × (B × C)) -×> ((A × B) × C)

  def wassocLR[A, B, C](using
    a: Obj[A], b: Obj[B], c: Obj[C],
  )[AB, AB_C, BC, A_BC](
    pAB: Prd[A, B, AB],
    pAB_C: Prd[AB, C, AB_C],
    pBC: Prd[B, C, BC],
    pA_BC: Prd[A, BC, A_BC],
  ): AB_C -> A_BC =
    iassocLR[\[A], \[B], \[C]](using PrdN.atom[A], PrdN.atom[B], PrdN.atom[C])
      .extract[AB_C, A_BC](
        PrdN(pAB_C)(PrdN.lift(pAB), PrdN.atom[C]),
        PrdN(pA_BC)(PrdN.atom[A], PrdN.lift(pBC)),
      )

  def wassocRL[A, B, C](using
    a: Obj[A], b: Obj[B], c: Obj[C],
  )[BC, A_BC, AB, AB_C](
    pBC: Prd[B, C, BC],
    pA_BC: Prd[A, BC, A_BC],
    pAB: Prd[A, B, AB],
    pAB_C: Prd[AB, C, AB_C],
  ): A_BC -> AB_C =
    iassocRL[\[A], \[B], \[C]](using PrdN.atom[A], PrdN.atom[B], PrdN.atom[C])
      .extract[A_BC, AB_C](
        PrdN(pA_BC)(PrdN.atom[A], PrdN.lift(pBC)),
        PrdN(pAB_C)(PrdN.lift(pAB), PrdN.atom[C]),
      )

  /** Given two witnesses that `P` and `Q` are each the tensor of `A` and `B`,
    * prove that `P` and `Q` are equal.
    */
  def tensorUniq[A, B, P, Q](p: Prd[A, B, P], q: Prd[A, B, Q]): P =:= Q

  def wfst[X, Y](f: X -> Y)[Z](using z: Obj[Z])(using x: Obj[X], y: Obj[Y])[P, Q](
    pSrc: Prd[X, Z, P],
    pTgt: Prd[Y, Z, Q],
  ): P -> Q =
    wpar(f, id[Z])(pSrc, pTgt)

  def wsnd[X](using x: Obj[X])[Y, Z](f: Y -> Z)(using y: Obj[Y], z: Obj[Z])[P, Q](
    pSrc: Prd[X, Y, P],
    pTgt: Prd[X, Z, Q],
  ): P -> Q =
    wpar(id[X], f)(pSrc, pTgt)
}

object NarrowWSemigroupalCategory {
  /** Pro forma (intensional) unary product marker (used to mark leafs of a binary product tree). */
  sealed trait \[A]

  /** Pro forma (intensional) binary product marker. */
  sealed trait ×[A, B]
}
