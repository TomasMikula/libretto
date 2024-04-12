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

  // private type AccBox[G <: AnyKind, X <: AnyKind] =
  //   Box[AccBox.Code, G :: X :: TNil]

  // private object AccBox:
  //   type Code = [⋅⋅[_]] =>> [G0[_ <: ⋅⋅[K]], X0 <: ⋅⋅[K]] =>> G0[X0]

  //   transparent inline def packer =
  //     Box.packer[Code]

  //   transparent inline def unpacker =
  //     Box.unpacker[Code]

  // /** Returns `[G[_]] => (G[A]) => ([X, Y] => (G[X], F[X, Y]) => G[Y]) => G[B]`. */
  // transparent inline def foldLeft =
  //   decodeExpr[F :: A :: B :: TNil](
  //     [⋅⋅[_], F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K]] => (
  //       thiz: AListK[K, F, A, B],
  //       packG: [G[_ <: ⋅⋅[K]], T <: ⋅⋅[K]] => G[T] => Box[[⋅⋅[_]] =>> [H[_ <: ⋅⋅[K]], X <: ⋅⋅[K]] =>> H[X], G :: T :: TNil],
  //       unpackG: [G[_ <: ⋅⋅[K]], T <: ⋅⋅[K]] => Box[[⋅⋅[_]] =>> [H[_ <: ⋅⋅[K]], X <: ⋅⋅[K]] =>> H[X], G :: T :: TNil] => G[T],
  //       liftF: [G[_ <: ⋅⋅[K]]] => ([X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (G[X], F[X, Y]) => G[Y]) =>
  //         Box[[⋅⋅[_]] =>> [G[_ <: ⋅⋅[K]]] =>> [X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (AccBox[G, X], Elem[K, F, X, Y]) => AccBox[G, Y], G :: TNil]
  //     ) =>
  //         [G[_ <: ⋅⋅[K]]] =>
  //           (ga: G[A]) =>
  //           (f: [X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (G[X], F[X, Y]) => G[Y]) =>
  //             // val gaBox = packG[G, A](ga)
  //             // val ff    = liftF[G](f)
  //             // val gbBox = thiz.foldLeftBoxed[G](packG[G, A](ga), liftF[G](f))
  //             unpackG[G, B](thiz.foldLeftBoxed[G](packG[G, A](ga), liftF[G](f)))
  //   )(
  //     this,
  //     AccBox.packer,
  //     AccBox.unpacker,
  //     decodeExpr[F :: TNil](
  //       [⋅⋅[_], F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]]] => (
  //         pack: [G[_ <: ⋅⋅[K]], A <: ⋅⋅[K]] => G[A] => AccBox[G, A],
  //         unpack: [G[_ <: ⋅⋅[K]], A <: ⋅⋅[K]] => AccBox[G, A] => G[A],
  //         unpackElem: [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K]] => Elem[K, F, A, B] => F[A, B],
  //         packF: [G[_ <: ⋅⋅[K]]] => ([X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (AccBox[G, X], Elem[K, F, X, Y]) => AccBox[G, Y]) =>
  //           Box[[⋅⋅[_]] =>> [G[_ <: ⋅⋅[K]]] =>> [X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (AccBox[G, X], Elem[K, F, X, Y]) => AccBox[G, Y], G :: TNil]
  //       ) =>
  //         [G[_ <: ⋅⋅[K]]] => (f: [X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (G[X], F[X, Y]) => G[Y]) =>
  //           packF[G](
  //             [X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (gx: AccBox[G, X], fxy: Elem[K, F, X, Y]) =>
  //               pack(f[X, Y](unpack(gx), unpackElem(fxy)))
  //           )
  //     )(
  //       AccBox.packer,
  //       AccBox.unpacker,
  //       Box.unpacker[Elem.Code[K]],
  //       Box.packer[[⋅⋅[_]] =>> [G[_ <: ⋅⋅[K]]] =>> [X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (AccBox[G, X], Elem[K, F, X, Y]) => AccBox[G, Y]],
  //     )
  //   )

  // def foldLeftBoxed[G <: AnyKind](
  //   ga: AccBox[G, A],
  //   f:  Box[[⋅⋅[_]] =>> [G[_ <: ⋅⋅[K]]] =>> [X <: ⋅⋅[K], Y <: ⋅⋅[K]] => (AccBox[G, X], Elem[K, F, X, Y]) => AccBox[G, Y], G :: TNil],
  // ): AccBox[G, B] =
  //   this match
  //     case AListK.Empty(ev) =>
  //       ev match
  //         case TypeEqK.Refl() => ga
  //     case cons: AListK.Cons[k, f, a, x, b] =>
  //       val f1 = Box.unpack(f)
  //       val gx = f1.polyFunApply[a :: x :: TNil, AccBox[G, x]](ga, cons.head)
  //       cons.tail.foldLeftBoxed(gx, f)
}

object AListK {
  type Elem[K, F <: AnyKind, A <: AnyKind, B <: AnyKind] =
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
