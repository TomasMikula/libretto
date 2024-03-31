package kindville.lib

import kindville.*

/** Kind-polymorphic type-aligned list. */
sealed trait AListK[K, F <: AnyKind, A <: AnyKind, B <: AnyKind] {
  import AListK.*

  /** Returns `[Z] => F[Z, A] => AListK[K, F, Z, B]`. */
  transparent inline def :: =
    decodeExpr[F :: A :: B :: TNil](
      [⋅⋅[_], F[_, _], A, B] => (
        thiz: AListK[K, F, A, B],
        cons: [F[_, _], A, B, C] => (F[A, B], AListK[K, F, B, C]) => AListK[K, F, A, C],
      ) =>
        [Z] => (h: F[Z, A]) => cons[F, Z, A, B](h, thiz)
    )(
      this,
      AListK.cons[K]
    )

  private type AccBox[G <: AnyKind, X <: AnyKind] =
    Box[[⋅⋅[_]] =>> [G0[_ <: ⋅⋅[K]], X0 <: ⋅⋅[K]] =>> G0[X0], G :: X :: TNil]
}

object AListK {
  opaque type Elem[K, F <: AnyKind, A <: AnyKind, B <: AnyKind] =
    Box[Elem.Code[K], F :: A :: B :: TNil]

  private object Elem {
    type Code[K] =
      [⋅⋅[_]] =>> [
        F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]],
        A <: ⋅⋅[K],
        B <: ⋅⋅[K],
      ] =>>
        F[A, B]
  }

  /** Returns `[F[_, _], A, B] => F[A, B] => Elem[K, F, A, B]` */
  transparent inline def elem[K] =
    Box.packer[Elem.Code[K]]

  case class Empty[K, F <: AnyKind, A <: AnyKind, B <: AnyKind](
    ev: TypeEqK[K, A, B]
  ) extends AListK[K, F, A, B]

  case class Cons[K, F <: AnyKind, A <: AnyKind, B <: AnyKind, C <: AnyKind](
    head: Elem[K, F, A, B],
    tail: AListK[K, F, B, C],
  ) extends AListK[K, F, A, C]

  /** Returns `[F[_, _], A] => Unit => AListK[K, F, A, A]` */
  transparent inline def empty[K] =
    decodeExpr[TNil](
      [⋅⋅[_]] =>
        (refl: [A <: ⋅⋅[K]] => Unit => TypeEqK[K, A, A]) =>
          [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K]] => (_: Unit) =>
            Empty[K, F, A, A](
              refl[A](())
            )
    )(
      TypeEqK.refl[K],
    )

  /** Returns `[F[_, _], A, B, C] => (F[A, B], AListK[K, F, B, C]) => AListK[K, F, A, C]` */
  transparent inline def cons[K] =
    decodeExpr[TNil](
      [⋅⋅[_]] =>
        (elem: [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K]] => F[A, B] => Elem[K, F, A, B]) =>
          [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K], C <: ⋅⋅[K]] => (
            h: F[A, B],
            t: AListK[K, F, B, C]
          ) =>
            Cons[K, F, A, B, C](elem(h), t)
    )(
      elem[K],
    )

  /** Returns `[F[_, _], A, B] => F[A, B] => AListK[K, F, A, B]` */
  transparent inline def single[K] =
    decodeExpr[TNil](
      [⋅⋅[_]] => (
        elem:  [F[_, _], A, B]    => F[A, B]                       => Elem[K, F, A, B],
        empty: [F[_, _], A]       => Unit                          => AListK[K, F, A, A],
        cons:  [F[_, _], A, B, C] => (F[A, B], AListK[K, F, B, C]) => AListK[K, F, A, C],
      ) =>
        [F[_, _], A, B] => (h: F[A, B]) => cons(h, empty[F, B](()))
    )(
      elem[K],
      empty[K],
      cons[K],
    )
}
