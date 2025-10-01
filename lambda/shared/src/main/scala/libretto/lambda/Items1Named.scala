package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, Exists, SingletonType, TypeEq}
import libretto.lambda.util.Exists.Indeed
import libretto.lambda.util.TypeEq.Refl

/** Data types for working with non-empty heterogeneous lists of named items of the form
 *
 *    "name1" :: T1 || ... || "nameN" :: Tn
 *
 * where `||` is the separator of items (associates to the left)
 * and `::` represents a type annotation.
 *
 * Analogous to [[Items1]], except for *named* items.
 *
 * Unlike [[Items1]], no special "`Nil`" type (list terminator) is needed,
 * as there is no ambiguity:
 *
 *  - `"x" :: (A || B)` is unambiguously a single-item list;
 *  - `"x" :: A || "y" :: B` is unambiguously a two-item list.
 *
 * whereas in unnamed version without `Nil` terminator, both cases above
 * would reduce `A || B`. (NB: With `Nil` terminator, they reduce to two
 * distinct types. `Nil || (A || B)` and `(Nil || A) || B`, respectively.)
 */
object Items1Named {

  /** Witnesses that `Items` is a list of `name :: type` pairs,
   * i.e. that `Items` is of the form `(Name1 :: T1) || ... || (NameN :: TN)`.
   */
  sealed trait Witness[||[_, _], ::[_, _], Items]

  object Witness {
    case class Single[||[_, _], ::[_, _], Lbl <: String, A](
      lbl: SingletonType[Lbl],
    ) extends Witness[||, ::, Lbl :: A]

    case class Snoc[||[_, _], ::[_, _], Init, Lbl <: String, A](
      init: Witness[||, ::, Init],
      lbl: SingletonType[Lbl],
    ) extends Witness[||, ::, Init || (Lbl :: A)]

    given single[||[_, _], ::[_, _], Lbl <: String, A](using
      lbl: SingletonType[Lbl],
    ): Witness[||, ::, Lbl :: A] =
      Single(lbl)

    given snoc[||[_, _], ::[_, _], Init, Lbl <: String, A](using
      init: Witness[||, ::, Init],
      lbl: SingletonType[Lbl],
    ): Witness[||, ::, Init || (Lbl :: A)] =
      Snoc(init, lbl)
  }

  // TODO: use to implement Member and Sum
  /** Holds `F[K, V]` for `K :: V` one of `Cases`,
   * where `Cases` is of the form `(K1 :: V1) || (K2 :: V2) || ...`
   * (where `||` associates to the left).
   */
  sealed trait OneOf[||[_, _], ::[_, _], F[_, _], Cases] {
    type Key
    type Type

    def value: F[Key, Type]

    def aux: this.type & OneOf.Aux[||, ::, F, Cases, Key, Type]

    def covary[G[x, y] >: F[x, y]]: OneOf[||, ::, G, Cases]

    def inInit[Kn, Vn]: OneOf.Aux[||, ::, F, Cases || Kn :: Vn, Key, Type] =
      OneOf.InInit(this.aux)

    infix def testMatching[G[_, _]](that: OneOf[||, ::, G, Cases])(using
      BiInjective[||],
      BiInjective[::],
    ): Option[(this.Key =:= that.Key, this.Type =:= that.Type)] =
      ???
  }

  object OneOf {
    sealed trait Aux[||[_, _], ::[_, _], F[_, _], Cases, K, V] extends OneOf[||, ::, F, Cases] {
      type Key = K
      type Type = V
    }

    case class Single[||[_, _], ::[_, _], F[_, _], K, V](value: F[K, V]) extends OneOf.Aux[||, ::, F, K :: V, K, V]:
      override def aux: this.type & Aux[||, ::, F, K :: V, K, V] = this
      override def covary[G[x,y] >: F[x, y]]: OneOf[||, ::, G, K :: V] = Single(value)

    case class Last[||[_, _], ::[_, _], F[_, _], Init, K, V](value: F[K, V]) extends OneOf.Aux[||, ::, F, Init || K :: V, K, V]:
      override def aux: this.type & Aux[||, ::, F, Init || K :: V, K, V] = this
      override def covary[G[x,y] >: F[x, y]]: OneOf[||, ::, G, Init || K :: V] = Last(value)

    case class InInit[||[_, _], ::[_, _], F[_, _], Ki, Vi, Init, Kn, Vn](
      init: OneOf.Aux[||, ::, F, Init, Ki, Vi],
    ) extends OneOf.Aux[||, ::, F, Init || Kn :: Vn, Ki, Vi]:
      override def aux: this.type & Aux[||, ::, F, Init || Kn :: Vn, Ki, Vi] = this
      override def value: F[Ki, Vi] = init.value
      override def covary[G[x,y] >: F[x, y]]: OneOf[||, ::, G, Init || Kn :: Vn] = InInit(init.covary[G].aux)

    def single[||[_, _], ::[_, _], F[_, _], K, V](value: F[K, V]): OneOf.Aux[||, ::, F, K :: V, K, V] =
      Single(value)

    def last[||[_, _], ::[_, _], F[_, _], Init, K, V](value: F[K, V]): OneOf.Aux[||, ::, F, Init || K :: V, K, V] =
      Last(value)

    type Member[||[_, _], ::[_, _], K, V, Cases] =
      Aux[||, ::, [K, V] =>> Any, Cases, K, V]

    object Member {
      def single[||[_, _], ::[_, _], K, V]: Member[||, ::, K, V, K :: V] =
        Single[||, ::, [K, V] =>> Any, K, V](())

      def last[||[_, _], ::[_, _], Init, K, V]: Member[||, ::, K, V, Init || K :: V] =
        Last[||, ::, [K, V] =>> Any, Init, K, V](())
    }
  }

  /**
    * Witnesses that `Label :: A` is one of `Cases`,
    * where `Cases` is of the form `(lbl1 :: A1) || (lbl2 :: A2) || ...`
    * (where `||` associates to the left).
    */
  sealed trait Member[||[_, _], ::[_, _], Label, A, Cases] {
    import Member.*

    final type Type = A

    def label: SingletonType[Label & String]

    given typeWitness: A =:= Type =
      <:<.refl

    def inInit[BLbl, B]: Member[||, ::, Label, A, Cases || (BLbl :: B)] =
      InInit(this)

    infix def testEqual[Lbl2, B](that: Member[||, ::, Lbl2, B, Cases])(using BiInjective[||],  BiInjective[::]): Option[A =:= B]

    protected def testEqualToSingle[Lbl2, B](using Cases =:= (Lbl2 :: B), BiInjective[::]): Option[A =:= B]

    protected def testEqualToInHead[I, Lbl2, B](using Cases =:= (I || (Lbl2 :: B)), BiInjective[||], BiInjective[::]): Option[A =:= B]

    private[Member] def asSingle[LB, B](using Cases =:= (LB :: B), BiInjective[::]): (SingletonType[Label], Label =:= LB, A =:= B)

    private[Member] def asMultiple[Init, LZ, Z](using
      Cases =:= (Init || LZ :: Z),
      BiInjective[||],
      BiInjective[::],
    ): Either[
      (SingletonType[Label], Label =:= LZ, A =:= Z),
      Member[||, ::, Label, A, Init]
    ]
  }

  object Member {
    case class InLast[||[_, _], ::[_, _], Init, Label <: String, A](
      label: SingletonType[Label],
    ) extends Member[||, ::, Label, A, Init || (Label :: A)] {
      override def testEqual[Lbl2, B](
        that: Member[||, ::, Lbl2, B, Init || (Label :: A)],
      )(using
        BiInjective[||],
        BiInjective[::],
      ): Option[A =:= B] =
        that.testEqualToInHead[Init, Label, A].map(_.flip)

      override protected def testEqualToInHead[I, Lbl2, B](using
        ev: (Init || (Label :: A)) =:= (I || (Lbl2 :: B)),
        i: BiInjective[||],
        j: BiInjective[::],
      ): Option[A =:= B] =
        ev match { case BiInjective[||](_, BiInjective[::](_, ev1)) => Some(ev1) }

      override protected def testEqualToSingle[Lbl2, B](using
        (Init || (Label :: A)) =:= (Lbl2 :: B),
        BiInjective[::],
      ): Option[A =:= B] =
        None

      override def asSingle[LB, B](using
        (Init || (Label :: A)) =:= (LB :: B),
        BiInjective[::],
      ): (SingletonType[Label], Label =:= LB, A =:= B) =
        throw new AssertionError("Impossible if `||` and `::` are different class types.")

      override def asMultiple[Init1, LZ, Z](using
        ev: (Init || Label :: A) =:= (Init1 || LZ :: Z),
        i: BiInjective[||],
        j: BiInjective[::],
      ): Either[
        (SingletonType[Label], Label =:= LZ, A =:= Z),
        Member[||, ::, Label, A, Init1]
      ] =
        ev match
          case BiInjective[||](TypeEq(Refl()), BiInjective[::](TypeEq(Refl()), TypeEq(Refl()))) =>
            Left((label, summon, summon))
    }

    case class Single[||[_, _], ::[_, _], Label <: String, A](
      label: SingletonType[Label],
    ) extends Member[||, ::, Label, A, Label :: A] {
      override def testEqual[Lbl2, B](that: Member[||, ::, Lbl2, B, Label :: A])(using BiInjective[||], BiInjective[::]): Option[A =:= B] =
        that.testEqualToSingle[Label, A].map(_.flip)

      override protected def testEqualToSingle[Lbl2, B](using
        ev: (Label :: A) =:= (Lbl2 :: B),
        inj: BiInjective[::],
      ): Option[A =:= B] =
        ev match { case BiInjective[::](_, ev1) => Some(ev1) }

      override protected def testEqualToInHead[I, Lbl2, B](using
        (Label :: A) =:= (I || (Lbl2 :: B)),
        BiInjective[||],
        BiInjective[::],
      ): Option[A =:= B] =
        None

      override def asSingle[LB, B](using
        ev: (Label :: A) =:= (LB :: B),
        inj: BiInjective[::],
      ): (SingletonType[Label], Label =:= LB, A =:= B) =
        val BiInjective[::](ev1, ev2) = ev
        (label, ev1, ev2)

      override def asMultiple[Init, LZ, Z](using
        (Label :: A) =:= (Init || (LZ :: Z)),
        BiInjective[||],
        BiInjective[::],
      ): Either[(SingletonType[Label], Label =:= LZ, A =:= Z), Member[||, ::, Label, A, Init]] =
        throw AssertionError("Impossible if `||` and `::` are two distinct class types.")
    }

    case class InInit[||[_, _], ::[_, _], Label, A, Init, BLbl, B](
      i: Member[||, ::, Label, A, Init],
    ) extends Member[||, ::, Label, A, Init || (BLbl :: B)]:
      override def label: SingletonType[Label & String] = i.label

      override def testEqual[Lbl2, C](
        that: Member[||, ::, Lbl2, C, Init || (BLbl :: B)],
      )(using
        BiInjective[||],
        BiInjective[::],
      ): Option[A =:= C] =
        that match
          case InInit(j) => i testEqual j
          case _ => None

      override protected def testEqualToSingle[Lbl2, C](using
        (Init || (BLbl :: B)) =:= (Lbl2 :: C),
        BiInjective[::],
      ): Option[A =:= C] =
        None

      override protected def testEqualToInHead[I, Lbl2, C](using
        (Init || (BLbl :: B)) =:= (I || (Lbl2 :: C)),
        BiInjective[||],
        BiInjective[::],
      ): Option[A =:= C] =
        None

      override def asSingle[LC, C](using
        (Init || (BLbl :: B)) =:= (LC :: C),
        BiInjective[::],
      ): (SingletonType[Label], Label =:= LC, A =:= C) =
        throw new AssertionError("Impossible if `||` and `::` are different class types.")

      override def asMultiple[Init1, LZ, Z](using
        ev: (Init || BLbl :: B) =:= (Init1 || LZ :: Z),
        i1: BiInjective[||],
        i2: BiInjective[::],
      ): Either[(SingletonType[Label], Label =:= LZ, A =:= Z), Member[||, ::, Label, A, Init1]] =
        ev match
          case BiInjective[||](TypeEq(Refl()), BiInjective[::](TypeEq(Refl()), TypeEq(Refl()))) =>
            Right(i)

    given singleMember[||[_, _], ::[_, _], Lbl <: String, A](using
      label: SingletonType[Lbl],
    ): Member[||, ::, Lbl, A, Lbl :: A] =
      Member.Single(label)

    given lastMember[||[_, _], ::[_, _], Init, Lbl <: String, A](using
      lbl: SingletonType[Lbl],
    ): Member[||, ::, Lbl, A, Init || (Lbl :: A)] =
      Member.InLast(lbl)

    given initMember[||[_, _], ::[_, _], Lbl, A, Init, BLbl, B](using
      j: Member[||, ::, Lbl, A, Init],
    ): Member[||, ::, Lbl, A, Init || (BLbl :: B)] =
      Member.InInit(j)

    def asSingle[||[_, _], ::[_, _], LA, A, LB, B](
      m: Member[||, ::, LA, A, LB :: B],
    )(using
      BiInjective[::],
    ): (SingletonType[LA], LA =:= LB, A =:= B) =
      m.asSingle

    def asMultiple[||[_, _], ::[_, _], LA, A, Init, LZ, Z](
      m: Member[||, ::, LA, A, Init || LZ :: Z],
    )(using
      BiInjective[||],
      BiInjective[::],
    ): Either[
      (SingletonType[LA], LA =:= LZ, A =:= Z),
      Member[||, ::, LA, A, Init]
    ] =
      m.asMultiple

  }

  /** A data type that holds all items of the `Items`` list, each wrapped in `F[_]`.
   *
   * In other words, an n-ary tuple of *named* values `F[Ai]`,
   * where `Items = "name1" :: A1 || ... || "nameN" :: An`,
   * where `||` associates to the left.
   */
  sealed trait Product[||[_, _], ::[_, _], F[_], Items] {
    def get[LblX, X](m: Member[||, ::, LblX, X, Items])(using
      BiInjective[||],
      BiInjective[::],
    ): F[X]

    def getOption(item: String): Option[Exists[[X] =>> (Member[||, ::, item.type, X, Items], F[X])]]

    def dropNames[∙[_, _], Nil]: Exists[[Items0] =>> (
      DropNames[||, ::, ∙, Nil, Items, Items0],
      Items1.Product[∙, Nil, F, Items0],
    )]

    def foldMap[G[_]](
      baseCase: [Lbl <: String, A] => (SingletonType[Lbl], F[A]) => G[Lbl :: A],
      snocCase: [Init, Lbl <: String, A] => (G[Init], SingletonType[Lbl], F[A]) => G[Init || Lbl :: A],
    ): G[Items]

    def asSingle[LblX, X](using Items =:= (LblX :: X), BiInjective[::]): F[X]

    def translate[G[_]](h: [X] => F[X] => G[X]): Product[||, ::, G, Items] =
      foldMap[[X] =>> Product[||, ::, G, X]](
        [Lbl <: String, A] => (lbl, fa) => Product.single(lbl, h(fa)),
        [Init, Lbl <: String, A] => (init, lbl, fa) => Product.Snoc(init, lbl, h(fa)),
      )

    def translateA[M[_], G[_]](
      h: [X] => F[X] => M[G[X]],
    )(using
      M: Applicative[M],
    ): M[Product[||, ::, G, Items]] =
      foldMap[[X] =>> M[Product[||, ::, G, X]]](
        [Lbl <: String, A] => (lbl, fa) => h(fa).map(Product.single(lbl, _)),
        [Init, Lbl <: String, A] => (init, lbl, fa) => M.map2(init, h(fa))(Product.Snoc(_, lbl, _)),
      )

    def wipeTranslate[G[_]](h: [X] => F[X] => Exists[G]): Product[||, ::, G, ?] =
      foldMap[[X] =>> Product[||, ::, G, ?]](
        [Lbl <: String, A] => (lbl, fa) => Product.single(lbl, h(fa).value),
        [Init, Lbl <: String, A] => (init, lbl, fa) => Product.Snoc(init, lbl, h(fa).value),
      )

    def wipeTranslateA[M[_], G[_]](
      h: [X] => F[X] => M[Exists[G]],
    )(using
      M: Applicative[M],
    ): M[Product[||, ::, G, ?]] =
      foldMap[[X] =>> M[Product[||, ::, G, ?]]](
        [Lbl <: String, A] => (lbl, fa) => h(fa).map(eh => Product.single(lbl, eh.value)),
        [Init, Lbl <: String, A] => (init, lbl, fa) => M.map2(init, h(fa))((init, fx) => Product.Snoc(init, lbl, fx.value)),
      )

    def forall(p: [X] => F[X] => Boolean): Boolean =
      this match
        case Product.Single(_, fa) => p(fa)
        case Product.Snoc(init, _, fa) => p(fa) && init.forall(p)

    def covary[G[x] >: F[x]]: Product[||, ::, G, Items]
  }

  object Product {
    case class Single[||[_, _], ::[_, _], F[_], Lbl <: String, A](
      label: SingletonType[Lbl],
      value: F[A],
    ) extends Product[||, ::, F, Lbl :: A] {

      override def covary[G[x] >: F[x]]: Product[||, ::, G, Lbl :: A] =
        Single(label, value)

      override def get[LblX, X](m: Member[||, ::, LblX, X, Lbl :: A])(using
        BiInjective[||],
        BiInjective[::],
      ): F[X] =
        Member.asSingle(m) match
          case (lbl, TypeEq(Refl()), TypeEq(Refl())) =>
            value

      override def getOption(item: String): Option[Exists[[X] =>> (Member[||, ::, item.type, X, Lbl :: A], F[X])]] =
        if (item == label.value)
          summon[Lbl =:= Lbl].asInstanceOf[item.type =:= Lbl] match
            case TypeEq(Refl()) =>
              Some(Exists((Member.Single(label), value)))
        else
          None

      override def dropNames[∙[_, _], Nil]: Exists[[Items0] =>> (
        DropNames[||, ::, ∙, Nil, Lbl :: A, Items0],
        Items1.Product[∙, Nil, F, Items0],
      )] =
        Exists((
          DropNames.Single(),
          Items1.Product.Single(value)
        ))

      override def foldMap[G[_]](
        caseSingle: [Lbl <: String, A] => (SingletonType[Lbl], F[A]) => G[Lbl :: A],
        caseSnoc: [Init, Lbl <: String, A] => (G[Init], SingletonType[Lbl], F[A]) => G[Init || Lbl :: A],
      ): G[Lbl :: A] =
        caseSingle(label, value)

      override def asSingle[LblX, X](using
        ev: Lbl :: A =:= LblX :: X,
        inj: BiInjective[::],
      ): F[X] =
        ev match { case BiInjective[::](_, TypeEq(Refl())) => value }
    }

    def single[||[_, _], ::[_, _], F[_], A](
      lbl: String,
    )(
      value: F[A],
    ): Single[||, ::, F, lbl.type, A] =
      single(SingletonType(lbl), value)

    def single[||[_, _], ::[_, _], F[_], Lbl <: String, A](
      lbl: SingletonType[Lbl],
      value: F[A],
    ): Single[||, ::, F, Lbl, A] =
      Single[||, ::, F, Lbl, A](lbl, value)

    case class Snoc[||[_, _], ::[_, _], F[_], Init, Lbl <: String, A](
      init: Product[||, ::, F, Init],
      lastName: SingletonType[Lbl],
      lastElem: F[A],
    ) extends Product[||, ::, F, Init || Lbl :: A] {

      override def covary[G[x] >: F[x]]: Product[||, ::, G, Init || Lbl :: A] =
        Snoc(init.covary, lastName, lastElem)

      override def get[LblX, X](m: Member[||, ::, LblX, X, Init || Lbl :: A])(using
        BiInjective[||],
        BiInjective[::],
      ): F[X] =
        Member.asMultiple(m) match
          case Left((lbl, TypeEq(Refl()), TypeEq(Refl()))) => lastElem
          case Right(m1) => init.get(m1)

      override def getOption(item: String): Option[Exists[[X] =>> (Member[||, ::, item.type, X, Init || Lbl :: A], F[X])]] =
        if (item == lastName.value)
          summon[Lbl =:= Lbl].asInstanceOf[item.type =:= Lbl] match
            case TypeEq(Refl()) =>
              Some(Exists((Member.InLast(lastName), lastElem)))
        else
          init.getOption(item)
            .map { case Indeed((i, a)) => Indeed((i.inInit, a)) }

      override def dropNames[∙[_,_], Nil]: Exists[[Items0] =>> (
        DropNames[||, ::, ∙, Nil, Init || Lbl :: A, Items0],
        Items1.Product[∙, Nil, F[_], Items0]
      )] =
        init.dropNames[∙, Nil] match
          case Indeed((drop0, sink0)) =>
            Exists((drop0.inInit[Lbl, A], Items1.Product.Snoc(sink0, lastElem)))

      override def foldMap[G[_]](
        caseSingle: [Lbl <: String, A] => (SingletonType[Lbl], F[A]) => G[Lbl :: A],
        caseSnoc: [Init, Lbl <: String, A] => (G[Init], SingletonType[Lbl], F[A]) => G[Init || Lbl :: A],
      ): G[Init || Lbl :: A] =
        caseSnoc(
          init.foldMap(caseSingle, caseSnoc),
          lastName,
          lastElem
        )

      override def asSingle[LblX, X](using (Init || Lbl :: A) =:= LblX :: X, BiInjective[::]): F[X] =
        // TODO: require evidence that `||` and `::` cannot possibly be equal.
        throw AssertionError(s"Impossible (A || B) =:= (C :: D), assuming || and :: are distinct class types (are they?).")
    }
  }

  /** A data type that holds one items of the `Items`` list, wrapped in `F[_]`. */
  sealed trait Sum[||[_, _], ::[_, _], F[_], Items] {
    type Label <: String
    type Case

    def tag: Member[||, ::, Label, Case, Items]
    def value: F[Case]
    def label: Label = tag.label.value

    def getSingle[K, V](using Items =:= (K :: V), BiInjective[::]): F[V]

    def covary[G[x] >: F[x]]: Sum[||, ::, G, Items]
  }

  object Sum {
    case class Value[||[_, _], ::[_, _], F[_], Lbl <: String, A, Items](
      tag: Member[||, ::, Lbl, A, Items],
      value: F[A],
    ) extends Sum[||, ::, F, Items] {
      override type Label = Lbl
      override type Case = A

      override def getSingle[K, V](using ev: Items =:= K :: V, i: BiInjective[::]): F[V] =
        val (_, _, ev2) = Member.asSingle(ev.substituteCo(tag))
        ev2.substituteCo(value)

      override def covary[G[x] >: F[x]]: Sum[||, ::, G, Items] =
        Value(tag, value)
    }
  }
}
