package kindville.lib

import kindville.*

/** Kind-polymorphic type-aligned list. */
sealed trait AListK[K, F <: AnyKind, A <: AnyKind, B <: AnyKind] {
  import AListK.*

  /** Returns `[Z] => F[Z, A] => AListK[K, F, Z, B]`. */
  transparent inline def :: =
    decodeT[F :: A :: B :: TNil](
      [⋅⋅[_]] => k ?=> [F[_, _], A, B] => () =>
        val thiz: AListK[K, F, A, B] =
          k.splice(this)
        val cons: [F[_, _], A, B, C] => (F[A, B], AListK[K, F, B, C]) => AListK[K, F, A, C] =
          k.splice(AListK.cons[K])
        [Z] => (h: F[Z, A]) => cons[F, Z, A, B](h, thiz)
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

  case class Empty[K, F <: AnyKind, A <: AnyKind, B <: AnyKind](
    ev: TypeEqK[K, A, B]
  ) extends AListK[K, F, A, B]

  case class Cons[K, F <: AnyKind, A <: AnyKind, B <: AnyKind, C <: AnyKind](
    head: Arrow[K, F, A, B],
    tail: AListK[K, F, B, C],
  ) extends AListK[K, F, A, C]

  /** Returns `[F[_, _], A] => () => AListK[K, F, A, A]` */
  transparent inline def empty[K] =
    decode(
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=>
        val refl: [A <: ⋅⋅[K]] => () => TypeEqK[K, A, A] =
          k.splice(TypeEqK.refl[K])
        [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K]] => () =>
          Empty[K, F, A, A](
            refl[A]()
          )
    )

  /** Returns `[F[_, _], A, B, C] => (F[A, B], AListK[K, F, B, C]) => AListK[K, F, A, C]` */
  transparent inline def cons[K] =
    decode(
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=>
        val elem: [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K]] => F[A, B] => Arrow[K, F, A, B] =
          k.splice(Arrow.packer[K])
        [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K], C <: ⋅⋅[K]] => (
          h: F[A, B],
          t: AListK[K, F, B, C]
        ) =>
          Cons[K, F, A, B, C](elem(h), t)
    )

  /** Returns `[F[_, _], A, B] => F[A, B] => AListK[K, F, A, B]` */
  transparent inline def single[K] =
    decode(
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=>
        val empty: [F[_, _], A]       => ()                            => AListK[K, F, A, A] = k.splice(AListK.empty[K])
        val cons:  [F[_, _], A, B, C] => (F[A, B], AListK[K, F, B, C]) => AListK[K, F, A, C] = k.splice(AListK.cons[K])
        [F[_, _], A, B] => (h: F[A, B]) => cons(h, empty[F, B]())
    )

  inline def foldLeft[K, G <: AnyKind, F <: AnyKind, A <: AnyKind, B <: AnyKind](
    ga: App[K, G, A],
    fs: AListK[K, F, A, B],
    action: Action[K, G, F],
  ): App[K, G, B] =
    def go[X <: AnyKind](acc: App[K, G, X], fs: AListK[K, F, X, B]): App[K, G, B] =
      fs match
        case Empty(ev) =>
          decodeT[F :: G :: X :: B :: TNil](
            [⋅⋅[_]] => kuotes ?=> [F0[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], G0[_ <: ⋅⋅[K]], X0 <: ⋅⋅[K], B0 <: ⋅⋅[K]] => () =>
              val subst: [M[_ <: ⋅⋅[K]]] => M[X0] => M[B0] =
                kuotes.splice(ev.substituteCo)
              val acc0: App[K, G0, X0] =
                kuotes.splice(acc)
              subst[[T <: ⋅⋅[K]] =>> App[K, G0, T]](acc0) : App[K, G0, B0]
          )
            .typecheckAs[App[K, G, B]]
        case Cons(f0, fs) =>
          val acc1 = action(acc, f0)
          go(acc1, fs)

    go(ga, fs)
}
