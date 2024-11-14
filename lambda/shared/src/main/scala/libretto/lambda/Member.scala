package libretto.lambda

import libretto.lambda.util.{BiInjective, StaticValue, TypeEq}
import libretto.lambda.util.TypeEq.Refl

sealed trait Member[||[_, _], ::[_, _], Label, A, Cases] {
  import Member.*

  final type Type = A

  def label: Label & String

  def inInit[BLbl, B]: Member[||, ::, Label, A, Cases || (BLbl :: B)] =
    InInit(this)

  infix def testEqual[Lbl2, B](that: Member[||, ::, Lbl2, B, Cases])(using BiInjective[||],  BiInjective[::]): Option[A =:= B]

  protected def testEqualToSingle[Lbl2, B](using Cases =:= (Lbl2 :: B), BiInjective[::]): Option[A =:= B]

  protected def testEqualToInHead[I, Lbl2, B](using Cases =:= (I || (Lbl2 :: B)), BiInjective[||], BiInjective[::]): Option[A =:= B]

  private[Member] def asSingle[LB, B](using Cases =:= (LB :: B), BiInjective[::]): (Label, Label =:= LB, A =:= B)

  private[Member] def asMultiple[Init, LZ, Z](using
    Cases =:= (Init || LZ :: Z),
    BiInjective[||],
    BiInjective[::],
  ): Either[
    (Label, Label =:= LZ, A =:= Z),
    Member[||, ::, Label, A, Init]
  ]
}

object Member {
  case class InLast[||[_, _], ::[_, _], Init, Label <: String, A](
    label: Label,
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
    ): (Label, Label =:= LB, A =:= B) =
      throw new AssertionError("Impossible if `||` and `::` are different class types.")

    override def asMultiple[Init1, LZ, Z](using
      ev: (Init || Label :: A) =:= (Init1 || LZ :: Z),
      i: BiInjective[||],
      j: BiInjective[::],
    ): Either[
      (Label, Label =:= LZ, A =:= Z),
      Member[||, ::, Label, A, Init1]
    ] =
      ev match
        case BiInjective[||](TypeEq(Refl()), BiInjective[::](TypeEq(Refl()), TypeEq(Refl()))) =>
          Left((label, summon, summon))
  }

  case class Single[||[_, _], ::[_, _], Label <: String, A](
    label: Label,
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

    override def asSingle[LB, B](using ev: Label :: A =:= LB :: B, inj: BiInjective[::]): (Label, Label =:= LB, A =:= B) =
      val BiInjective[::](ev1, ev2) = ev
      (label, ev1, ev2)

    override def asMultiple[Init, LZ, Z](using
      (Label :: A) =:= (Init || (LZ :: Z)),
      BiInjective[||],
      BiInjective[::],
    ): Either[(Label, Label =:= LZ, A =:= Z), Member[||, ::, Label, A, Init]] =
      throw AssertionError("Impossible if `||` and `::` are two distinct class types.")
  }

  case class InInit[||[_, _], ::[_, _], Label, A, Init, BLbl, B](
    i: Member[||, ::, Label, A, Init],
  ) extends Member[||, ::, Label, A, Init || (BLbl :: B)]:
    override def label: Label & String = i.label

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
    ): (Label, Label =:= LC, A =:= C) =
      throw new AssertionError("Impossible if `||` and `::` are different class types.")

    override def asMultiple[Init1, LZ, Z](using
      ev: (Init || BLbl :: B) =:= (Init1 || LZ :: Z),
      i1: BiInjective[||],
      i2: BiInjective[::],
    ): Either[(Label, Label =:= LZ, A =:= Z), Member[||, ::, Label, A, Init1]] =
      ev match
        case BiInjective[||](TypeEq(Refl()), BiInjective[::](TypeEq(Refl()), TypeEq(Refl()))) =>
          Right(i)

  given singleInjector[||[_, _], ::[_, _], Lbl <: String, A](using
    label: StaticValue[Lbl],
  ): Member[||, ::, Lbl, A, Lbl :: A] =
    Member.Single(label.value)

  given lastInjector[||[_, _], ::[_, _], Init, Lbl <: String, A](using
    lbl: StaticValue[Lbl],
  ): Member[||, ::, Lbl, A, Init || (Lbl :: A)] =
    Member.InLast(lbl.value)

  given initInjector[||[_, _], ::[_, _], Lbl, A, Init, BLbl, B](using
    j: Member[||, ::, Lbl, A, Init],
  ): Member[||, ::, Lbl, A, Init || (BLbl :: B)] =
    Member.InInit(j)

  def asSingle[||[_, _], ::[_, _], LA, A, LB, B](
    m: Member[||, ::, LA, A, LB :: B],
  )(using
    BiInjective[::],
  ): (LA, LA =:= LB, A =:= B) =
    m.asSingle

  def asMultiple[||[_, _], ::[_, _], LA, A, Init, LZ, Z](
    m: Member[||, ::, LA, A, Init || LZ :: Z],
  )(using
    BiInjective[||],
    BiInjective[::],
  ): Either[
    (LA, LA =:= LZ, A =:= Z),
    Member[||, ::, LA, A, Init]
  ] =
    m.asMultiple

}
