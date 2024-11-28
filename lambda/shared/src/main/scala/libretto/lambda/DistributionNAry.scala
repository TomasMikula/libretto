package libretto.lambda

import libretto.lambda.util.{BiInjective, Exists, TypeEq}
import libretto.lambda.util.TypeEq.Refl

trait DistributionNAry[->[_, _], **[_, _], Enum[_], ||[_, _], ::[_, _]] {
  import DistributionNAry.*

  val cat: SemigroupalCategory[->, **]

  type DistLR[A, Cases] = DistributionNAry.DistLR[**, ||, ::, A, Cases]
  type DistRL[B, Cases] = DistributionNAry.DistRL[**, ||, ::, B, Cases]

  def distLR[A, Cases](ev: DistLR[A, Cases]): (A ** Enum[Cases]) -> Enum[ev.Out]
  def distRL[B, Cases](ev: DistRL[B, Cases]): (Enum[Cases] ** B) -> Enum[ev.Out]

  sealed trait DistF[F[_], Cases] {
    type Out
    def operationalize(f: Focus[**, F]): DistF.Operationalized[F, Cases] { type Out = DistF.this.Out }

    // TODO: to be fully general, case handlers should take an additional evidence about the output type (Out =:= ...).
    def fold[H[F[_], Cases, Out]](
      caseSingle: [LblX <: String, X] => ((LblX :: X) =:= Cases) ?=> DistF.Single[F, LblX, X] => H[F, LblX :: X, LblX :: F[X]],
      caseSnoc: [Init, LblX <: String, X, FInit] => ((Init || LblX :: X) =:= Cases) ?=> DistF.Snoc[F, Init, LblX, X, FInit] => H[F, Init || (LblX :: X), FInit || (LblX :: F[X])],
    ): H[F, Cases, Out]
  }

  object DistF {
    case class Single[F[_], Lbl <: String, A](
      label: Lbl,
    ) extends DistF[F, Lbl :: A] {
      override type Out = Lbl :: F[A]
      override def operationalize(f: Focus[**, F]): Operationalized[F, Lbl :: A]{type Out = Lbl :: F[A]} =
        f match
          case Focus.Id() =>
            Operationalized.Id[Lbl :: A]()
          case f: Focus.Fst[pr, f1, b] =>
            val d1: Operationalized[f1, Lbl :: A]{type Out = Lbl :: f1[A]} =
              Single[f1, Lbl, A](label).operationalize(f.i)
            Operationalized.DistSnd[f1, b, Lbl :: A, Lbl :: f1[A], Lbl :: F[A]](d1, DistRL.Single(label))
          case f: Focus.Snd[pr, f2, a] =>
            val d2: Operationalized[f2, Lbl :: A]{type Out = Lbl :: f2[A]} =
              Single[f2, Lbl, A](label).operationalize(f.i)
            Operationalized.DistFst[a, f2, Lbl :: A, Lbl :: f2[A], Lbl :: F[A]](d2, DistLR.Single(label))

      override def fold[H[_[_], _, _]](
        caseSingle: [LblX <: String, X] => (LblX :: X =:= Lbl :: A) ?=> Single[F, LblX, X] => H[F, LblX :: X, LblX :: F[X]],
        caseSnoc: [Init, LblX <: String, X, FInit] => ((Init || LblX :: X) =:= (Lbl :: A)) ?=> Snoc[F, Init, LblX, X, FInit] => H[F, Init || LblX :: X, FInit || LblX :: F[X]],
      ): H[F, Lbl :: A, Lbl :: F[A]] =
        caseSingle[Lbl, A](this)
    }

    case class Snoc[F[_], Init, Lbl <: String, A, FInit](
      init: DistF[F, Init] { type Out = FInit },
      lbl: Lbl,
    ) extends DistF[F, Init || (Lbl :: A)] {
      override type Out = FInit || (Lbl :: F[A])
      override def operationalize(f: Focus[**, F]): Operationalized[F, Init || (Lbl :: A)]{type Out = FInit || (Lbl :: F[A])} =
        init.operationalize(f).extend[Lbl, A](lbl)

      override def fold[H[_[_], _, _]](
        caseSingle: [LblX <: String, X] => ((LblX :: X) =:= (Init || Lbl :: A)) ?=> Single[F, LblX, X] => H[F, LblX :: X, LblX :: F[X]],
        caseSnoc: [I, LblX <: String, X, FI] => ((I || LblX :: X) =:= (Init || Lbl :: A)) ?=> Snoc[F, I, LblX, X, FI] => H[F, I || LblX :: X, FI || LblX :: F[X]],
      ): H[F, Init || (Lbl :: A), Out] =
        caseSnoc[Init, Lbl, A, FInit](this)
    }

    /** Like [[DistF]], witnesses that distributing `F` into `Cases` yields `Out`.
     *  Unlike [[DistF]], [[Operationalized]] is defined by induction over the structure of `F`
     *  (as opposed to by induction over `Cases`). As such, it can be more readily used
     *  to generate the distributing function `F[OneOf[Cases]] -> OneOf[Out]`.
     */
    sealed trait Operationalized[F[_], Cases] { self =>
      type Out
      def extend[Lbl <: String, B](lbl: Lbl): Operationalized[F, Cases || (Lbl :: B)]{type Out = self.Out || (Lbl :: F[B])}
      def compile: F[Enum[Cases]] -> Enum[Out]
    }

    object Operationalized {

      case class Id[Cases]() extends DistF.Operationalized[[x] =>> x, Cases] {
        override type Out = Cases
        override def extend[ZLbl <: String, Z](zLbl: ZLbl): Operationalized[[x] =>> x, Cases || (ZLbl :: Z)]{type Out = Cases || (ZLbl :: Z)} =
          Id[Cases || (ZLbl :: Z)]()
        override def compile: Enum[Cases] -> Enum[Cases] =
          cat.id[Enum[Cases]]
      }

      case class DistFst[A, F2[_], Cases, F2Cases, Res](
        distF2: DistF.Operationalized[F2, Cases] { type Out = F2Cases },
        dist1: DistLR[A, F2Cases] { type Out = Res },
      ) extends DistF.Operationalized[[x] =>> A ** F2[x], Cases] {
        override type Out = Res
        override def extend[Lbl <: String, Z](lbl: Lbl): Operationalized[[x] =>> A ** F2[x], Cases || (Lbl :: Z)]{type Out = Res || (Lbl :: (A ** F2[Z]))} =
          val inner: Operationalized[F2, Cases || (Lbl :: Z)]{type Out = F2Cases || (Lbl :: F2[Z])} =
            distF2.extend[Lbl, Z](lbl)
          val outer: DistLR[A, F2Cases || (Lbl :: F2[Z])]{type Out = Res || (Lbl :: (A ** F2[Z]))} =
            dist1.extend[Lbl, F2[Z]](lbl)
          DistFst[A, F2, Cases || (Lbl :: Z), F2Cases || (Lbl :: F2[Z]), Res || (Lbl :: (A ** F2[Z]))](
            inner,
            outer,
          )
        override def compile: (A ** F2[Enum[Cases]]) -> Enum[Res] =
          import cat.{andThen, id, par}
          andThen(
            par(
              id[A],
              distF2.compile
            ),
            distLR(dist1),
          )
      }

      case class DistSnd[F1[_], B, Cases, F1Cases, Res](
        distF1: DistF.Operationalized[F1, Cases] { type Out = F1Cases },
        dist2: DistRL[B, F1Cases] { type Out = Res },
      ) extends DistF.Operationalized[[x] =>> F1[x] ** B, Cases] {
        override type Out = Res
        override def extend[Lbl <: String, Z](lbl: Lbl): Operationalized[[x] =>> F1[x] ** B, Cases || (Lbl :: Z)]{type Out = Res || (Lbl :: (F1[Z] ** B))} =
          val inner: Operationalized[F1, Cases || (Lbl :: Z)]{type Out = F1Cases || (Lbl :: F1[Z])} =
            distF1.extend[Lbl, Z](lbl)
          val outer: DistRL[B, F1Cases || (Lbl :: F1[Z])]{type Out = Res || (Lbl :: (F1[Z] ** B))} =
            dist2.extend[Lbl, F1[Z]](lbl)
          DistSnd(inner, outer)
        override def compile: (F1[Enum[Cases]] ** B) -> Enum[Res] =
          import cat.{andThen, id, par}
          andThen(
            par(
              distF1.compile,
              id[B]
            ),
            distRL(dist2)
          )
      }
    }

    def intoCases[F[_], Cases](cases: ItemList[||, ::, Cases]): DistF[F, Cases] =
      cases match
        case s: ItemList.Single[sep, of, lbl, a] =>
          DistF.Single[F, lbl, a](s.lbl)
        case s: ItemList.Snoc[sep, of, init, lbl, a] =>
          val init: DistF[F, init] = intoCases(s.init)
          DistF.Snoc[F, init, lbl, a, init.Out](init, s.lbl)
  }
}

object DistributionNAry {

  sealed trait DistLR[**[_, _], ||[_, _], ::[_, _], A, Cases] { self =>
    type Out

    def extend[Lbl <: String, Z](
      lbl: Lbl,
    ): DistLR[**, ||, ::, A, Cases || (Lbl :: Z)] { type Out = self.Out || (Lbl :: (A ** Z)) } =
      DistLR.Snoc(this, lbl)

    def distributeOver[N, I](
      m: Member[||, ::, N, I, Cases],
    )(using
      BiInjective[||],
      BiInjective[::],
    ): Member[||, ::, N, A ** I, Out]
  }

  object DistLR {
    case class Single[**[_, _], ||[_, _], ::[_, _], A, Lbl <: String, B](
      label: Lbl,
    ) extends DistLR[**, ||, ::, A, Lbl :: B] {
      override type Out = Lbl :: (A ** B)

      override def distributeOver[N, I](
        m: Member[||, ::, N, I, Lbl :: B],
      )(using
        BiInjective[||],
        BiInjective[::],
      ): Member[||, ::, N, A ** I, Out] =
        Member.asSingle(m) match
          case (lbl, TypeEq(Refl()), TypeEq(Refl())) =>
            Member.Single(lbl)
    }

    case class Snoc[**[_, _], ||[_, _], ::[_, _], A, Init, Lbl <: String, Z, AInit](
      init: DistLR[**, ||, ::, A, Init] { type Out = AInit },
      lbl: Lbl,
    ) extends DistLR[**, ||, ::, A, Init || (Lbl :: Z)] {
      override type Out = AInit || (Lbl :: (A ** Z))

      override def distributeOver[N, I](
        m: Member[||, ::, N, I, Init || Lbl :: Z],
      )(using
        BiInjective[||],
        BiInjective[::],
      ): Member[||, ::, N, A ** I, Out] =
        Member.asMultiple(m) match
          case Left((lbl, TypeEq(Refl()), TypeEq(Refl()))) =>
            Member.InLast(lbl)
          case Right(m1) =>
            init.distributeOver(m1).inInit
    }
  }

  sealed trait DistRL[**[_, _], ||[_, _], ::[_, _], B, Cases] { self =>
    type Out

    def extend[Lbl <: String, Z](
      lbl: Lbl,
    ): DistRL[**, ||, ::, B, Cases || (Lbl :: Z)] { type Out = self.Out || (Lbl :: (Z ** B)) } =
      DistRL.Snoc(this, lbl)

    def dropNames[∙[_, _], Nil]: Exists[[X] =>> Exists[[Y] =>> (
      DropNames[||, ::, ∙, Nil, Cases, X],
      DistRL.Unnamed[**, ∙, Nil, B, X] { type Out = Y },
      DropNames[||, ::, ∙, Nil, Out, Y],
    )]]
  }

  object DistRL {
    case class Single[**[_, _], ||[_, _], ::[_, _], B, Lbl <: String, A](
      label: Lbl,
    ) extends DistRL[**, ||, ::, B, Lbl :: A] {
      override type Out = Lbl :: (A ** B)

      override def dropNames[∙[_,_], Nil]: Exists[[X] =>> Exists[[Y] =>> (
        DropNames[||, ::, ∙, Nil, Lbl :: A, X],
        DistRL.Unnamed[**, ∙, Nil, B, X] { type Out = Y },
        DropNames[||, ::, ∙, Nil, Out, Y],
      )]] =
        Exists(Exists((
          DropNames.Single(),
          DistRL.Unnamed.Single[**, ∙, Nil, B, A](),
          DropNames.Single(),
        )))
    }

    case class Snoc[**[_, _], ||[_, _], ::[_, _], B, Init, Lbl <: String, Z, BInit](
      init: DistRL[**, ||, ::, B, Init] { type Out = BInit },
      lbl: Lbl,
    ) extends DistRL[**, ||, ::, B, Init || (Lbl :: Z)] {
      override type Out = BInit || (Lbl :: (Z ** B))

      override def dropNames[∙[_,_], Nil]: Exists[[X] =>> Exists[[Y] =>> (
        DropNames[||, ::, ∙, Nil, Init || Lbl :: Z, X],
        DistRL.Unnamed[**, ∙, Nil, B, X] { type Out = Y },
        DropNames[||, ::, ∙, Nil, Out, Y],
      )]] =
        init.dropNames[∙, Nil] match {
          case Exists.Some(Exists.Some((x, d, y))) =>
            Exists(Exists((
              x.inInit[Lbl, Z],
              DistRL.Unnamed.Snoc(d),
              y.inInit[Lbl, Z ** B],
            )))
        }
    }

    sealed trait Unnamed[**[_, _], ∙[_, _], Nil, D, Cases] {
      type Out

      def kernel: ParN[∙, Nil, [x, y] =>> (x ** D) =:= y, Cases, Out]
    }

    object Unnamed {
      case class Single[**[_, _], ∙[_, _], Nil, D, A]()
        extends DistRL.Unnamed[**, ∙, Nil, D, Nil ∙ A] {

        override type Out = Nil ∙ (A ** D)

        override def kernel: ParN[∙, Nil, [x, y] =>> (x ** D) =:= y, Nil ∙ A, Nil ∙ (A ** D)] =
          ParN.Single(summon[A ** D =:= A ** D])
      }

      case class Snoc[**[_, _], ∙[_, _], Nil, D, Init, Last, DInit](
        init: DistRL.Unnamed[**, ∙, Nil, D, Init] { type Out = DInit },
      ) extends DistRL.Unnamed[**, ∙, Nil, D, Init ∙ Last] {
        override type Out = DInit ∙ (Last ** D)

        override def kernel: ParN[∙, Nil, [x, y] =>> (x ** D) =:= y, Init ∙ Last, DInit ∙ (Last ** D)] =
          init.kernel ∙ summon[Last ** D =:= Last ** D]
      }
    }
  }

  def fromBinary[->[_, _], **[_, _], ++[_, _], Enum[_], ||[_, _], ::[_, _]](
    inj: [Label, A, Cases] => Member[||, ::, Label, A, Cases] => (A -> Enum[Cases]),
    peel: [Init, Label, Z] => DummyImplicit ?=> Enum[Init || (Label :: Z)] -> (Enum[Init] ++ Z),
    unpeel: [Init, Label, Z] => DummyImplicit ?=> (Enum[Init] ++ Z) -> Enum[Init || (Label :: Z)],
    extract: [Label, A] => DummyImplicit ?=> Enum[Label :: A] -> A,
  )(using
    c: SemigroupalCategory[->, **],
    cocat: CocartesianSemigroupalCategory[->, ++],
    distr: Distribution[->, **, ++],
  ): DistributionNAry[->, **, Enum, ||, ::] =
    new DistributionNAry[->, **, Enum, ||, ::] {
      override val cat = c

      import cat.*
      import cocat.{either, injectL, injectR}

      override def distLR[A, Cases](d: this.DistLR[A, Cases]): (A ** Enum[Cases]) -> Enum[d.Out] =
        d match
          case s: (DistLR.Single[**, ||, ::, a, l, b] & d.type) =>
            summon[Cases =:= (l :: b)]
            val ev = summon[d.Out =:= s.Out]
            val f: (A ** Enum[Cases]) -> Enum[s.Out] = distLRSingle(s)
            f.to(using ev.flip.liftCo[Enum])
          case s: (DistLR.Snoc[**, ||, ::, a, init, l, z, aInit] & d.type) =>
            summon[Cases =:= (init || l :: z)]
            val ev = summon[d.Out =:= s.Out]
            val f: (A ** Enum[Cases]) -> Enum[s.Out] = distLRSnoc(s)
            f.to(using ev.flip.liftCo[Enum])

      private def distLRSingle[A, Lbl <: String, B](
        d: DistLR.Single[**, ||, ::, A, Lbl, B],
      ): (A ** Enum[Lbl :: B]) -> Enum[d.Out] =
        extract[Lbl, B].inSnd[A] > inj(Member.Single(d.label))

      private def distLRSnoc[A, Init, LblZ <: String, Z, AInit](
        d: DistLR.Snoc[**, ||, ::, A, Init, LblZ, Z, AInit],
      ): (A ** Enum[Init || LblZ :: Z]) -> Enum[d.Out] =
        cat.snd(peel[Init, LblZ, Z]) > distr.distLR > either(
          distLR(d.init) > injectL > unpeel[AInit, LblZ, A ** Z],
          inj(Member.InLast(d.lbl)),
        )

      override def distRL[B, Cases](d: this.DistRL[B, Cases]): (Enum[Cases] ** B) -> Enum[d.Out] =
        d match
          case s: (DistRL.Single[**, ||, ::, b, l, a] & d.type) =>
            summon[Cases =:= (l :: a)]
            val ev = summon[d.Out =:= s.Out]
            val f: (Enum[Cases] ** B) -> Enum[s.Out] = distRLSingle(s)
            f.to(using ev.flip.liftCo[Enum])
          case s: (DistRL.Snoc[**, ||, ::, b, init, l, z, bInit] & d.type) =>
            summon[Cases =:= (init || l :: z)]
            val ev = summon[d.Out =:= s.Out]
            val f: (Enum[Cases] ** B) -> Enum[s.Out] = distRLSnoc(s)
            f.to(using ev.flip.liftCo[Enum])

      private def distRLSingle[B, Lbl <: String, A](
        d: DistRL.Single[**, ||, ::, B, Lbl, A],
      ): (Enum[Lbl :: A] ** B) -> Enum[d.Out] =
        extract[Lbl, A].inFst[B] > inj(Member.Single(d.label))

      private def distRLSnoc[B, Init, LblZ <: String, Z, BInit](
        d: DistRL.Snoc[**, ||, ::, B, Init, LblZ, Z, BInit],
      ): (Enum[Init || LblZ :: Z] ** B) -> Enum[d.Out] =
        cat.fst(peel[Init, LblZ, Z]) > distr.distRL > either(
          distRL(d.init) > injectL > unpeel[BInit, LblZ, Z ** B],
          inj(Member.InLast(d.lbl)),
        )
    }
}
