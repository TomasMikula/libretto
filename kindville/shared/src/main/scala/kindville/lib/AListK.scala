package kindville.lib

import kindville.*

/** Kind-polymorphic type-aligned list. */
sealed trait AListK[K, F <: AnyKind, A <: AnyKind, B <: AnyKind] {
  import AListK.*

  /** Returns `[Z] => F[Z, A] => AListK[K, F, Z, B]`. */
  transparent inline def :: =
    decodeT[F :: A :: B :: TNil](
      [⋅⋅[_]] => k ?=> [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K]] => () =>
        val thiz: AListK[K, F, ⋅⋅[A], ⋅⋅[B]] =
          k.splice(this)
        val cons: [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K], C <: ⋅⋅[K]] => (F[A, B], AListK[K, F, ⋅⋅[B], ⋅⋅[C]]) => (⋅⋅[B] ofKinds K) ?=> AListK[K, F, ⋅⋅[A], ⋅⋅[C]] =
          k.splice(AListK.cons[K])
        [Z <: ⋅⋅[K]] => (h: F[Z, A]) => (ev: ⋅⋅[A] ofKinds K) ?=> cons[F, Z, A, B](h, thiz)
    )
}

object AListK {

  case class Empty[K, F <: AnyKind, A <: AnyKind, B <: AnyKind](
    ev: TypeEqK[K, A, B]
  ) extends AListK[K, F, A, B]

  case class Cons[K, F <: AnyKind, A <: AnyKind, B <: AnyKind, C <: AnyKind](
    head: Arrow[K, F, A, B],
    tail: AListK[K, F, B, C],
  )(using
    ev: B ofKinds K,
  ) extends AListK[K, F, A, C] {
    type Pivot = B

    given pivotKind: B ofKinds K = ev
  }

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

  /** Returns `[F[_, _], A, B, C] => (F[A, B], AListK[K, F, B, C]) => (B ofKinds K) ?=> AListK[K, F, A, C]` */
  transparent inline def cons[K] =
    decode(
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=>
        val elem: [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K]] => F[A, B] => Arrow[K, F, ⋅⋅[A], ⋅⋅[B]] =
          k.splice(Arrow.packer[K])
        [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K], C <: ⋅⋅[K]] => (
          h: F[A, B],
          t: AListK[K, F, ⋅⋅[B], ⋅⋅[C]]
        ) => (ev: ⋅⋅[B] ofKinds K) ?=>
          Cons[K, F, ⋅⋅[A], ⋅⋅[B], ⋅⋅[C]](elem(h), t)(using ev)
    )

  /** Returns `[F[_, _], A, B] => F[A, B] => (⋅⋅[B] ofKinds K) ?=> AListK[K, F, A, B]` */
  transparent inline def single[K] =
    decode(
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=>
        val empty: [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K]]                         => ()                                                          => AListK[K, F, ⋅⋅[A], ⋅⋅[A]] = k.splice(AListK.empty[K])
        val cons:  [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K], C <: ⋅⋅[K]] => (F[A, B], AListK[K, F, ⋅⋅[B], ⋅⋅[C]]) => (⋅⋅[B] ofKinds K) ?=> AListK[K, F, ⋅⋅[A], ⋅⋅[C]] = k.splice(AListK.cons[K])
        [F[_ <: ⋅⋅[K], _ <: ⋅⋅[K]], A <: ⋅⋅[K], B <: ⋅⋅[K]] => (h: F[A, B]) => (ev: ⋅⋅[B] ofKinds K) ?=> cons(h, empty[F, B]())
    )

  inline def foldLeft[K, G <: AnyKind, F <: AnyKind, A <: AnyKind, B <: AnyKind](
    ga: App[K, G, A],
    fs: AListK[K, F, A, B],
    action: Action[K, G, F],
  )(using
    A ofKinds K,
    B ofKinds K,
    G ofKinds (K -> *),
  ): App[K, G, B] =
    def go[X <: AnyKind](acc: App[K, G, X], fs: AListK[K, F, X, B])(using X ofKinds K): App[K, G, B] =
      fs match
        case Empty(ev) =>
          ev.substituteCoAppDynamic[G](acc)
        case c @ Cons(f0, fs) =>
          import c.given
          val acc1 = action.applyDynamic[X, c.Pivot](acc, f0)
          go[c.Pivot](acc1, fs)

    go(ga, fs)
}
