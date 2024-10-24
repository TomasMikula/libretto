package libretto.lambda

import libretto.lambda.util.{BiInjective, StaticValue}

sealed trait Member[||[_, _], ::[_, _], Label, A, Cases] {
  import Member.*

  final type Type = A

  def label: Label & String

  def inInit[BLbl, B]: Member[||, ::, Label, A, Cases || (BLbl :: B)] =
    InInit(this)

  infix def testEqual[Lbl2, B](that: Member[||, ::, Lbl2, B, Cases])(using BiInjective[||],  BiInjective[::]): Option[A =:= B]

  protected def testEqualToSingle[Lbl2, B](using Cases =:= (Lbl2 :: B), BiInjective[::]): Option[A =:= B]

  protected def testEqualToInHead[I, Lbl2, B](using Cases =:= (I || (Lbl2 :: B)), BiInjective[||], BiInjective[::]): Option[A =:= B]
}

object Member {
  case class InLast[||[_, _], ::[_, _], Init, Label <: String, A](
    label: Label,
  ) extends Member[||, ::, Label, A, Init || (Label :: A)]:
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

  case class Single[||[_, _], ::[_, _], Label <: String, A](
    label: Label,
  ) extends Member[||, ::, Label, A, Label :: A]:
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
}
