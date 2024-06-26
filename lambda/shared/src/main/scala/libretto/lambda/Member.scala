package libretto.lambda

import libretto.lambda.util.{BiInjective, StaticValue}

sealed trait Member[||[_, _], ::[_, _], Label, A, Cases] {
  import Member.*

  final type Type = A

  def label: Label & String

  def inTail[HLbl, H]: Member[||, ::, Label, A, (HLbl :: H) || Cases] =
    InTail(this)

  infix def testEqual[Lbl2, B](that: Member[||, ::, Lbl2, B, Cases])(using BiInjective[||],  BiInjective[::]): Option[A =:= B]

  protected def testEqualToSingle[Lbl2, B](using Cases =:= (Lbl2 :: B), BiInjective[::]): Option[A =:= B]

  protected def testEqualToInHead[Lbl2, B, T](using Cases =:= ((Lbl2 :: B) || T), BiInjective[||], BiInjective[::]): Option[A =:= B]
}

object Member {
  case class InHead[||[_, _], ::[_, _], Label <: String, A, Tail](
    label: Label,
  ) extends Member[||, ::, Label, A, (Label :: A) || Tail]:
    override def testEqual[Lbl2, B](that: Member[||, ::, Lbl2, B, (Label :: A) || Tail])(using BiInjective[||], BiInjective[::]): Option[A =:= B] =
      that.testEqualToInHead[Label, A, Tail].map(_.flip)

    override protected def testEqualToInHead[Lbl2, B, T](using
      ev: (Label :: A || Tail) =:= (Lbl2 :: B || T),
      i: BiInjective[||],
      j: BiInjective[::],
    ): Option[A =:= B] =
      ev match { case BiInjective[||](BiInjective[::](_, ev1), _) => Some(ev1) }

    override protected def testEqualToSingle[Lbl2, B](using (Label :: A || Tail) =:= (Lbl2 :: B), BiInjective[::]): Option[A =:= B] =
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

    override protected def testEqualToInHead[Lbl2, B, T](using (Label :: A) =:= (Lbl2 :: B || T), BiInjective[||], BiInjective[::]): Option[A =:= B] =
      None

  case class InTail[||[_, _], ::[_, _], Label, A, HLbl, H, Tail](
    i: Member[||, ::, Label, A, Tail],
  ) extends Member[||, ::, Label, A, (HLbl :: H) || Tail]:
    override def label: Label & String = i.label

    override def testEqual[Lbl2, B](
      that: Member[||, ::, Lbl2, B, (HLbl :: H) || Tail],
    )(using
      BiInjective[||],
      BiInjective[::],
    ): Option[A =:= B] =
      that match
        case InTail(j) => i testEqual j
        case _ => None

    override protected def testEqualToSingle[Lbl2, B](using (HLbl :: H || Tail) =:= (Lbl2 :: B), BiInjective[::]): Option[A =:= B] =
      None

    override protected def testEqualToInHead[Lbl2, B, T](using (HLbl :: H || Tail) =:= (Lbl2 :: B || T), BiInjective[||], BiInjective[::]): Option[A =:= B] =
      None

  given singleInjector[||[_, _], ::[_, _], Lbl <: String, A](using
    label: StaticValue[Lbl],
  ): Member[||, ::, Lbl, A, Lbl :: A] =
    Member.Single(label.value)

  given headInjector[||[_, _], ::[_, _], HLbl <: String, H, Tail](using
    hLbl: StaticValue[HLbl],
  ): Member[||, ::, HLbl, H, (HLbl :: H) || Tail] =
    Member.InHead(hLbl.value)

  given tailInjector[||[_, _], ::[_, _], Lbl, A, HLbl, H, Tail](using
    j: Member[||, ::, Lbl, A, Tail],
  ): Member[||, ::, Lbl, A, (HLbl :: H) || Tail] =
    Member.InTail(j)
}
