package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, Exists, SingletonValue, TypeEq}
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
      lbl: SingletonValue[Lbl],
    ) extends Witness[||, ::, Lbl :: A]

    case class Snoc[||[_, _], ::[_, _], Init, Lbl <: String, A](
      init: Witness[||, ::, Init],
      lbl: SingletonValue[Lbl],
    ) extends Witness[||, ::, Init || (Lbl :: A)]

    given single[||[_, _], ::[_, _], Lbl <: String, A](using
      lbl: SingletonValue[Lbl],
    ): Witness[||, ::, Lbl :: A] =
      Single(lbl)

    given snoc[||[_, _], ::[_, _], Init, Lbl <: String, A](using
      init: Witness[||, ::, Init],
      lbl: SingletonValue[Lbl],
    ): Witness[||, ::, Init || (Lbl :: A)] =
      Snoc(init, lbl)
  }

  /**
    * Witnesses that `Label :: A` is one of `Cases`,
    * where `Cases` is of the form `(lbl1 :: A1) || (lbl2 :: A2) || ...`
    * (where `||` associates to the left).
    */
  sealed trait Member[||[_, _], ::[_, _], Label, A, Cases] {
    import Member.*

    final type Type = A

    def label: SingletonValue[Label & String]

    def inInit[BLbl, B]: Member[||, ::, Label, A, Cases || (BLbl :: B)] =
      InInit(this)

    infix def testEqual[Lbl2, B](that: Member[||, ::, Lbl2, B, Cases])(using BiInjective[||],  BiInjective[::]): Option[A =:= B]

    protected def testEqualToSingle[Lbl2, B](using Cases =:= (Lbl2 :: B), BiInjective[::]): Option[A =:= B]

    protected def testEqualToInHead[I, Lbl2, B](using Cases =:= (I || (Lbl2 :: B)), BiInjective[||], BiInjective[::]): Option[A =:= B]

    private[Member] def asSingle[LB, B](using Cases =:= (LB :: B), BiInjective[::]): (SingletonValue[Label], Label =:= LB, A =:= B)

    private[Member] def asMultiple[Init, LZ, Z](using
      Cases =:= (Init || LZ :: Z),
      BiInjective[||],
      BiInjective[::],
    ): Either[
      (SingletonValue[Label], Label =:= LZ, A =:= Z),
      Member[||, ::, Label, A, Init]
    ]
  }

  object Member {
    case class InLast[||[_, _], ::[_, _], Init, Label <: String, A](
      label: SingletonValue[Label],
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
      ): (SingletonValue[Label], Label =:= LB, A =:= B) =
        throw new AssertionError("Impossible if `||` and `::` are different class types.")

      override def asMultiple[Init1, LZ, Z](using
        ev: (Init || Label :: A) =:= (Init1 || LZ :: Z),
        i: BiInjective[||],
        j: BiInjective[::],
      ): Either[
        (SingletonValue[Label], Label =:= LZ, A =:= Z),
        Member[||, ::, Label, A, Init1]
      ] =
        ev match
          case BiInjective[||](TypeEq(Refl()), BiInjective[::](TypeEq(Refl()), TypeEq(Refl()))) =>
            Left((label, summon, summon))
    }

    case class Single[||[_, _], ::[_, _], Label <: String, A](
      label: SingletonValue[Label],
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
      ): (SingletonValue[Label], Label =:= LB, A =:= B) =
        val BiInjective[::](ev1, ev2) = ev
        (label, ev1, ev2)

      override def asMultiple[Init, LZ, Z](using
        (Label :: A) =:= (Init || (LZ :: Z)),
        BiInjective[||],
        BiInjective[::],
      ): Either[(SingletonValue[Label], Label =:= LZ, A =:= Z), Member[||, ::, Label, A, Init]] =
        throw AssertionError("Impossible if `||` and `::` are two distinct class types.")
    }

    case class InInit[||[_, _], ::[_, _], Label, A, Init, BLbl, B](
      i: Member[||, ::, Label, A, Init],
    ) extends Member[||, ::, Label, A, Init || (BLbl :: B)]:
      override def label: SingletonValue[Label & String] = i.label

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
      ): (SingletonValue[Label], Label =:= LC, A =:= C) =
        throw new AssertionError("Impossible if `||` and `::` are different class types.")

      override def asMultiple[Init1, LZ, Z](using
        ev: (Init || BLbl :: B) =:= (Init1 || LZ :: Z),
        i1: BiInjective[||],
        i2: BiInjective[::],
      ): Either[(SingletonValue[Label], Label =:= LZ, A =:= Z), Member[||, ::, Label, A, Init1]] =
        ev match
          case BiInjective[||](TypeEq(Refl()), BiInjective[::](TypeEq(Refl()), TypeEq(Refl()))) =>
            Right(i)

    given singleInjector[||[_, _], ::[_, _], Lbl <: String, A](using
      label: SingletonValue[Lbl],
    ): Member[||, ::, Lbl, A, Lbl :: A] =
      Member.Single(label)

    given lastInjector[||[_, _], ::[_, _], Init, Lbl <: String, A](using
      lbl: SingletonValue[Lbl],
    ): Member[||, ::, Lbl, A, Init || (Lbl :: A)] =
      Member.InLast(lbl)

    given initInjector[||[_, _], ::[_, _], Lbl, A, Init, BLbl, B](using
      j: Member[||, ::, Lbl, A, Init],
    ): Member[||, ::, Lbl, A, Init || (BLbl :: B)] =
      Member.InInit(j)

    def asSingle[||[_, _], ::[_, _], LA, A, LB, B](
      m: Member[||, ::, LA, A, LB :: B],
    )(using
      BiInjective[::],
    ): (SingletonValue[LA], LA =:= LB, A =:= B) =
      m.asSingle

    def asMultiple[||[_, _], ::[_, _], LA, A, Init, LZ, Z](
      m: Member[||, ::, LA, A, Init || LZ :: Z],
    )(using
      BiInjective[||],
      BiInjective[::],
    ): Either[
      (SingletonValue[LA], LA =:= LZ, A =:= Z),
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

    def dropNames[∙[_, _], Nil]: Exists[[Items0] =>> (
      DropNames[||, ::, ∙, Nil, Items, Items0],
      Items1.Product[∙, Nil, F, Items0],
    )]

    def foldMap[G[_]](
      baseCase: [Lbl <: String, A] => (SingletonValue[Lbl], F[A]) => G[Lbl :: A],
      snocCase: [Init, Lbl <: String, A] => (G[Init], SingletonValue[Lbl], F[A]) => G[Init || Lbl :: A],
    ): G[Items]

    def asSingle[LblX, X](using Items =:= (LblX :: X), BiInjective[::]): F[X]

    def translate[G[_]](h: [X] => F[X] => G[X]): Product[||, ::, G, Items] =
      foldMap[[X] =>> Product[||, ::, G, X]](
        [Lbl <: String, A] => (lbl, fa) => Product.single(lbl, h(fa)),
        [Init, Lbl <: String, A] => (init, lbl, fa) => Product.Snoc(init, lbl, h(fa)),
      )

    def translateA[G[_], H[_]](
      h: [X] => F[X] => G[H[X]],
    )(using
      G: Applicative[G],
    ): G[Product[||, ::, H, Items]] =
      foldMap[[X] =>> G[Product[||, ::, H, X]]](
        [Lbl <: String, A] => (lbl, fa) => h(fa).map(Product.single(lbl, _)),
        [Init, Lbl <: String, A] => (init, lbl, fa) => G.map2(init, h(fa))(Product.Snoc(_, lbl, _)),

      )

    def forall(p: [X] => F[X] => Boolean): Boolean =
      this match
        case Product.Single(_, fa) => p(fa)
        case Product.Snoc(init, _, fa) => p(fa) && init.forall(p)
  }

  object Product {
    case class Single[||[_, _], ::[_, _], F[_], Lbl <: String, A](
      label: SingletonValue[Lbl],
      value: F[A],
    ) extends Product[||, ::, F, Lbl :: A] {

      override def get[LblX, X](m: Member[||, ::, LblX, X, Lbl :: A])(using
        BiInjective[||],
        BiInjective[::],
      ): F[X] =
        Member.asSingle(m) match
          case (lbl, TypeEq(Refl()), TypeEq(Refl())) =>
            value

      override def dropNames[∙[_, _], Nil]: Exists[[Items0] =>> (
        DropNames[||, ::, ∙, Nil, Lbl :: A, Items0],
        Items1.Product[∙, Nil, F, Items0],
      )] =
        Exists((
          DropNames.Single(),
          Items1.Product.Single(value)
        ))

      override def foldMap[G[_]](
        caseSingle: [Lbl <: String, A] => (SingletonValue[Lbl], F[A]) => G[Lbl :: A],
        caseSnoc: [Init, Lbl <: String, A] => (G[Init], SingletonValue[Lbl], F[A]) => G[Init || Lbl :: A],
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
      single(SingletonValue(lbl), value)

    def single[||[_, _], ::[_, _], F[_], Lbl <: String, A](
      lbl: SingletonValue[Lbl],
      value: F[A],
    ): Single[||, ::, F, Lbl, A] =
      Single[||, ::, F, Lbl, A](lbl, value)

    case class Snoc[||[_, _], ::[_, _], F[_], Init, Lbl <: String, A](
      init: Product[||, ::, F, Init],
      lastName: SingletonValue[Lbl],
      lastElem: F[A],
    ) extends Product[||, ::, F, Init || Lbl :: A] {

      override def get[LblX, X](m: Member[||, ::, LblX, X, Init || Lbl :: A])(using
        BiInjective[||],
        BiInjective[::],
      ): F[X] =
        Member.asMultiple(m) match
          case Left((lbl, TypeEq(Refl()), TypeEq(Refl()))) => lastElem
          case Right(m1) => init.get(m1)

      override def dropNames[∙[_,_], Nil]: Exists[[Items0] =>> (
        DropNames[||, ::, ∙, Nil, Init || Lbl :: A, Items0],
        Items1.Product[∙, Nil, F[_], Items0]
      )] =
        init.dropNames[∙, Nil] match
          case Exists.Some((drop0, sink0)) =>
            Exists((drop0.inInit[Lbl, A], Items1.Product.Snoc(sink0, lastElem)))

      override def foldMap[G[_]](
        caseSingle: [Lbl <: String, A] => (SingletonValue[Lbl], F[A]) => G[Lbl :: A],
        caseSnoc: [Init, Lbl <: String, A] => (G[Init], SingletonValue[Lbl], F[A]) => G[Init || Lbl :: A],
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
  }

  object Sum {
    case class Value[||[_, _], ::[_, _], F[_], Lbl <: String, A, Items](
      tag: Member[||, ::, Lbl, A, Items],
      value: F[A],
    ) extends Sum[||, ::, F, Items] {
      override type Label = Lbl
      override type Case = A
    }
  }
}
