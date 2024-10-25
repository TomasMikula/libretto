package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, StaticValue, TypeEq, TypeEqK}
import libretto.lambda.util.TypeEqK.Refl
import libretto.lambda.util.unapply.Unapply

trait EnumModule[->[_, _], **[_, _], Enum[_], ||[_, _], ::[_, _]] {
  import EnumModule.*

  /** Witnesses that `Cases` is a list of cases, usable in `Enum`,
   * i.e. that `Cases` is of the form `(Name1 :: T1) || ... || (NameN :: TN)`.
   */
  type CaseList[Cases]

  type IsCaseOf[Label, Cases] <: AnyRef with { type Type }
  type EnumPartition[Cases, P]
  type Handlers[Cases, R]
  type DistLR[A, Cases] <: { type Out }
  type DistRL[B, Cases] <: { type Out }
  type DistF[F[_], Cases] <: { type Out }

  def inject[Cases](label: String)(using c: IsCaseOf[label.type, Cases]): c.Type -> Enum[Cases]

  def make[ADT](using u: Unapply[ADT, Enum])(label: String)(using c: IsCaseOf[label.type, u.A]): c.Type -> ADT =
    u.ev.flip.substituteCo(
      inject[u.A](label)
    )

  def handle[Cases, R](handlers: Handlers[Cases, R]): Enum[Cases] -> R

  def handle[ADT](using u: Unapply[ADT, Enum]): HandleInit[u.A] =
    HandleInit[u.A]

  class HandleInit[Cases]:
    def apply[R](handlers: Handlers.InitialBuilder[Cases] => Handlers[Cases, R]): Enum[Cases] -> R =
      handle[Cases, R](handlers(Handlers[Cases]))

  def distF[F[_], Cases](using F: Focus[**, F], ev: DistF[F, Cases]): F[Enum[Cases]] -> Enum[ev.Out]

  def distLR[A, Cases](using ev: DistLR[A, Cases]): (A ** Enum[Cases]) -> Enum[ev.Out]

  def distRL[B, Cases](using ev: DistRL[B, Cases]): (Enum[Cases] ** B) -> Enum[ev.Out]

  given singleCaseList[Lbl <: String, A](using label: StaticValue[Lbl]): CaseList[Lbl :: A]
  given snocCaseList[Init, Lbl <: String, A](using init: CaseList[Init], lbl: StaticValue[Lbl]): CaseList[Init || (Lbl :: A)]

  given isSingleCase[Lbl <: String, A](using label: StaticValue[Lbl]): (IsCaseOf[Lbl, Lbl :: A] with { type Type = A })
  given isLastCase[Init, Lbl <: String, Z](using StaticValue[Lbl]): (IsCaseOf[Lbl, Init || (Lbl :: Z)] with { type Type = Z })
  given isInitCase[Lbl, Init, ZLbl, Z](using j: IsCaseOf[Lbl, Init]): (IsCaseOf[Lbl, Init || (ZLbl :: Z)] with { type Type = j.Type })

  given distLRSnoc[A, Init, Label <: String, Z](using
    init: DistLR[A, Init],
    label: StaticValue[Label],
  ): (DistLR[A, Init || (Label :: Z)] with { type Out = init.Out || (Label :: (A ** Z)) })

  given distLRSingle[A, Label <: String, B](using
    label: StaticValue[Label],
  ): (DistLR[A, Label :: B] with { type Out = Label :: (A ** B) })

  given distFSingle[F[_], Lbl <: String, A](using label: StaticValue[Lbl]): (DistF[F, Lbl :: A] with { type Out = Lbl :: F[A] })

  given distFSnoc[F[_], Init, Label <: String, Z](using
    init: DistF[F, Init],
    label: StaticValue[Label],
  ): (DistF[F, Init || (Label :: Z)] with { type Out = init.Out || (Label :: F[Z]) })

  val Handlers: HandlersModule

  trait HandlersModule {
    type Builder[Cases, RemainingCases, R]

    def single[Lbl, A, R](h: A -> R): Handlers[Lbl :: A, R]

    def snoc[Init, Lbl, Z, R](
      init: Handlers[Init, R],
      last: Z -> R,
    ): Handlers[Init || (Lbl :: Z), R]

    def apply[Cases, R]: Builder[Cases, Cases, R]

    def apply[Cases]: InitialBuilder[Cases] =
      ()

    /** Compared to [[Builder]], defers specifying the result type. */
    opaque type InitialBuilder[Cases] =
      Unit

    extension [Cases, Init, ZLbl, Z, R](b: Builder[Cases, Init || (ZLbl :: Z), R])
      def caseOf[Lbl](using StaticValue[Lbl], Lbl =:= ZLbl)(h: Z -> R): Builder[Cases, Init, R]

    extension [Cases, Lbl, A, R](b: Builder[Cases, Lbl :: A, R])
      def caseOf[L](using StaticValue[L], L =:= Lbl, DummyImplicit)(h: A -> R): Handlers[Cases, R]

    extension [Init, ZLbl, Z](b: InitialBuilder[Init || (ZLbl :: Z)])
      def caseOf[Lbl](using StaticValue[Lbl], Lbl =:= ZLbl): [R] => (Z -> R) => Builder[Init || (ZLbl :: Z), Init, R] =
        [R] => h => apply[Init || (ZLbl :: Z), R].caseOf[Lbl](h)

    extension [Lbl, A](b: InitialBuilder[Lbl :: A])
      def caseOf[L](using StaticValue[L], L =:= Lbl, DummyImplicit): [R] => (A -> R) => Handlers[Lbl :: A, R] =
       [R] => h => apply[Lbl :: A, R].caseOf[L](h)
  }

  type Partitioning[Cases] <: libretto.lambda.Partitioning[->, **, Enum[Cases]] {
    type Partition[P] = EnumPartition[Cases, P]
  }

  def partitioning[Cases](using ev: CaseList[Cases]): Partitioning[Cases]

  def partition[ADT](using
    u: Unapply[ADT, Enum],
    ev: CaseList[u.A],
  ): Partitioning[u.A] =
    partitioning[u.A]

  def toPartition[Cases, C](ev: IsCaseOf[C, Cases]): EnumPartition[Cases, ev.Type]

  def extractorOf[T, Cases](
    p: libretto.lambda.Partitioning[->, **, T] { type Partition[P] = EnumPartition[Cases, P] },
  )(
    label: String,
  )(using
    ev: IsCaseOf[label.type, Cases],
  ): Extractor[->, **, T, ev.Type] =
    Extractor(p, toPartition(ev))

  extension [Cases](p: Partitioning[Cases]) {
    def apply[C](using ev: IsCaseOf[C, Cases]): Extractor[->, **, Enum[Cases], ev.Type] =
      Extractor(p, toPartition(ev))
  }
}

object EnumModule {
  def fromBinarySums[->[_, _], **[_, _], ++[_, _], Enum[_], ||[_, _], ::[_, _]](
    inj: [Label, A, Cases] => Member[||, ::, Label, A, Cases] => (A -> Enum[Cases]),
    peel: [Init, Label, Z] => DummyImplicit ?=> Enum[Init || (Label :: Z)] -> (Enum[Init] ++ Z),
    unpeel: [Init, Label, Z] => DummyImplicit ?=> (Enum[Init] ++ Z) -> Enum[Init || (Label :: Z)],
    extract: [Label, A] => DummyImplicit ?=> Enum[Label :: A] -> A,
  )(using
    cat: SemigroupalCategory[->, **],
    cocat: CocartesianSemigroupalCategory[->, ++],
    distr: Distribution[->, **, ++],
    i: BiInjective[||],
    j: BiInjective[::],
  ): EnumModule[->, **, Enum, ||, ::] =
    EnumModuleFromBinarySums[->, **, ++, Enum, ||, ::](inj, peel, unpeel, extract)(cat, cocat, distr)
}

private[lambda] class EnumModuleFromBinarySums[->[_, _], **[_, _], ++[_, _], Enum[_], ||[_, _], ::[_, _]](
  inj: [Label, A, Cases] => Member[||, ::, Label, A, Cases] => (A -> Enum[Cases]),
  peel: [Cases, Label, Z] => DummyImplicit ?=> Enum[Cases || (Label :: Z)] -> (Enum[Cases] ++ Z),
  unpeel: [Cases, Label, Z] => DummyImplicit ?=> (Enum[Cases] ++ Z) -> Enum[Cases || (Label :: Z)],
  extract: [Label, A] => DummyImplicit ?=> Enum[Label :: A] -> A,
)(
  cat: SemigroupalCategory[->, **],
  cocat: CocartesianSemigroupalCategory[->, ++],
  distr: Distribution[->, **, ++],
)(using
  BiInjective[||],
  BiInjective[::],
) extends EnumModule[->, **, Enum, ||, ::] {
  import EnumModule.*
  import cocat.{either, injectL, injectR}

  given SemigroupalCategory[->, **] = cat

  private type Injector[Label, A, Cases] = libretto.lambda.Member[||, ::, Label, A, Cases]

  override opaque type CaseList[Cases] = CaseListImpl[Cases]

  override opaque type IsCaseOf[Label, Cases] <: { type Type } = Injector[Label, ?, Cases]
  override opaque type EnumPartition[Cases, P] = Injector[?, P, Cases]
  override opaque type Handlers[Cases, R] = HandlersImpl[Cases, R]
  override opaque type DistLR[A, Cases] <: { type Out } = DistLRImpl[A, Cases]
  override opaque type DistRL[B, Cases] <: { type Out } = DistRLImpl[B, Cases]
  override opaque type DistF[F[_], Cases] <: { type Out } = DistFImpl[F, Cases]

  override opaque type Partitioning[Cases] <: libretto.lambda.Partitioning[->, **, Enum[Cases]] {
    type Partition[P] = EnumPartition[Cases, P]
  } =
    PartitioningImpl[Cases]

  override def inject[Cases](label: String)(using c: IsCaseOf[label.type, Cases]): c.Type -> Enum[Cases] =
    inj[label.type, c.Type, Cases](c)

  override def handle[Cases, R](handlers: Handlers[Cases, R]): Enum[Cases] -> R =
    handlers.compile

  override def distF[F[_], Cases](using F: Focus[**, F], ev: DistF[F, Cases]): F[Enum[Cases]] -> Enum[ev.Out] =
    ev.operationalize(F).compile

  override def distLR[A, Cases](using ev: DistLR[A, Cases]): (A ** Enum[Cases]) -> Enum[ev.Out] =
    ev.compile

  override def distRL[B, Cases](using ev: DistRL[B, Cases]): (Enum[Cases] ** B) -> Enum[ev.Out] =
    ev.compile

  override given singleCaseList[Lbl <: String, A](using label: StaticValue[Lbl]): CaseList[Lbl :: A] =
    CaseListImpl.singleCase(label.value)
  override given snocCaseList[Init, Lbl <: String, A](using init: CaseList[Init], lbl: StaticValue[Lbl]): CaseList[Init || (Lbl :: A)] =
    CaseListImpl.snoc(init, lbl.value)

  override given isSingleCase[Lbl <: String, A](using label: StaticValue[Lbl]): (IsCaseOf[Lbl, Lbl :: A] with { type Type = A }) =
    Member.Single(label.value)

  override given isLastCase[Init, Lbl <: String, Z](using
    lbl: StaticValue[Lbl],
  ): (IsCaseOf[Lbl, Init || (Lbl :: Z)] with { type Type = Z }) =
    Member.InLast(lbl.value)

  override given isInitCase[Lbl, Init, ZLbl, Z](using
    j: IsCaseOf[Lbl, Init],
  ): (IsCaseOf[Lbl, Init || (ZLbl :: Z)] with { type Type = j.Type }) =
    Member.InInit(j)

  override given distLRSnoc[A, Init, Label <: String, Z](using
    init: DistLR[A, Init],
    label: StaticValue[Label],
  ): (DistLR[A, Init || (Label :: Z)] with { type Out = init.Out || (Label :: (A ** Z)) }) =
    DistLRImpl.snoc[A, Init, Label, Z](init, label.value)

  override given distLRSingle[A, Label <: String, B](using
    label: StaticValue[Label],
  ): (DistLR[A, Label :: B] with { type Out = Label :: (A ** B) }) =
    DistLRImpl.Single(label.value)

  override given distFSingle[F[_], Lbl <: String, A](using label: StaticValue[Lbl]): (DistF[F, Lbl :: A] with { type Out = Lbl :: F[A] }) =
    DistFImpl.Single(label.value)
  override given distFSnoc[F[_], Init, Label <: String, Z](using
    init: DistF[F, Init],
    label: StaticValue[Label],
  ): (DistF[F, Init || (Label :: Z)] with { type Out = init.Out || (Label :: F[Z]) }) =
    DistFImpl.Snoc(init, label.value)

  override object Handlers extends HandlersModule {

    override opaque type Builder[Cases, RemainingCases, R] =
      HandlersBuilder[Cases, RemainingCases, R]

    override def single[Lbl, A, R](h: A -> R): Handlers[Lbl :: A, R] =
      HandlersImpl.Single(h)

    override def snoc[Init, Lbl, Z, R](
      init: Handlers[Init, R],
      last: Z -> R,
    ): Handlers[Init || (Lbl :: Z), R] =
      HandlersImpl.Snoc(init, last)

    override def apply[Cases, R]: Builder[Cases, Cases, R] =
      HandlersBuilder.Empty()

    extension [Cases, Init, ZLbl, Z, R](b: Builder[Cases, Init || (ZLbl :: Z), R])
      def caseOf[Lbl](using StaticValue[Lbl], Lbl =:= ZLbl)(h: Z -> R): Builder[Cases, Init, R] =
        HandlersBuilder.addHandler(b, h)

    extension [Cases, Lbl, A, R](b: Builder[Cases, Lbl :: A, R])
      def caseOf[L](using StaticValue[L], L =:= Lbl, DummyImplicit)(h: A -> R): Handlers[Cases, R] =
        HandlersBuilder.build(b, h)
  }

  override def partitioning[Cases](using ev: CaseList[Cases]): Partitioning[Cases] =
    PartitioningImpl(ev)

  override def toPartition[Cases, C](
    ev: IsCaseOf[C, Cases],
  ): EnumPartition[Cases, ev.Type] =
    ev

  private sealed trait CaseListImpl[Cases]

  private object CaseListImpl {
    case class SingleCaseList[Lbl <: String, A](
      lbl: Lbl,
    ) extends CaseListImpl[Lbl :: A]

    case class SnocCaseList[Init, Lbl <: String, A](
      init: CaseList[Init],
      lbl: Lbl,
    ) extends CaseListImpl[Init || (Lbl :: A)]

    def singleCase[Lbl <: String, A](
      lbl: Lbl,
    ): CaseList[Lbl :: A] =
      SingleCaseList(lbl)

    def snoc[Init, Lbl <: String, A](
      init: CaseList[Init],
      lbl: Lbl,
    ): CaseList[Init || (Lbl :: A)] =
      SnocCaseList(init, lbl)
  }

  private sealed trait DistLRImpl[A, Cases] { self =>
    type Out

    def compile: (A ** Enum[Cases]) -> Enum[Out]

    def extend[Lbl <: String, Z](lbl: Lbl): DistLRImpl[A, Cases || (Lbl :: Z)]{type Out = self.Out || (Lbl :: (A ** Z))} =
      DistLRImpl.Snoc(this, lbl)
  }

  private object DistLRImpl {
    case class Single[A, Lbl <: String, B](label: Lbl) extends DistLRImpl[A, Lbl :: B] {
      override type Out = Lbl :: (A ** B)

      override def compile: (A ** Enum[Lbl :: B]) -> Enum[Out] =
        extract[Lbl, B].inSnd[A] > inj(Member.Single(label))
    }

    case class Snoc[A, Init, Lbl <: String, Z, AInit](
      init: DistLRImpl[A, Init] { type Out = AInit },
      lbl: Lbl,
    ) extends DistLRImpl[A, Init || (Lbl :: Z)] {
      override type Out = AInit || (Lbl :: (A ** Z))

      override def compile: (A ** Enum[Init || (Lbl :: Z)]) -> Enum[Out] =
        cat.snd(peel[Init, Lbl, Z]) > distr.distLR > either(
          init.compile > injectL > unpeel[AInit, Lbl, A ** Z],
          inj(Member.InLast(lbl)),
        )
    }

    def snoc[A, Init, Lbl <: String, Z](
      init: DistLRImpl[A, Init],
      lbl: Lbl,
    ): DistLRImpl[A, Init || (Lbl :: Z)] { type Out = init.Out || (Lbl :: (A ** Z)) } =
      Snoc[A, Init, Lbl, Z, init.Out](init, lbl)
  }

  private sealed trait DistRLImpl[B, Cases] { self =>
    type Out

    def compile: (Enum[Cases] ** B) -> Enum[Out]

    def extend[Lbl <: String, Z](lbl: Lbl): DistRLImpl[B, Cases || (Lbl :: Z)]{type Out = self.Out || (Lbl :: (Z ** B))} =
      DistRLImpl.Snoc(this, lbl)
  }

  private object DistRLImpl {
    case class Single[B, Lbl <: String, A](
      label: Lbl,
    ) extends DistRLImpl[B, Lbl :: A] {
      override type Out = Lbl :: (A ** B)

      override def compile: (Enum[Lbl :: A] ** B) -> Enum[Out] =
        extract[Lbl, A].inFst[B] > inj(Member.Single(label))
    }

    case class Snoc[B, Init, Lbl <: String, Z, BInit](
      init: DistRLImpl[B, Init] { type Out = BInit },
      lbl: Lbl,
    ) extends DistRLImpl[B, Init || (Lbl :: Z)] {
      override type Out = BInit || (Lbl :: (Z ** B))

      override def compile: (Enum[Init || (Lbl :: Z)] ** B) -> Enum[Out] =
        cat.fst(peel[Init, Lbl, Z]) > distr.distRL > either(
          init.compile > injectL > unpeel[BInit, Lbl, Z ** B],
          inj(Member.InLast(lbl)),
        )
    }
  }

  private sealed trait DistFImpl[F[_], Cases] {
    type Out
    def operationalize(f: Focus[**, F]): DistFImpl.Operationalized[F, Cases] { type Out = DistFImpl.this.Out }

    def foldA[G[_], H[_]](
      mapA: [LblX, X] => Injector[LblX, X, Cases] => G[H[LblX :: F[X]]],
      snoc: [FInit, LblX, X] => (H[FInit], H[LblX :: F[X]]) => H[FInit || (LblX :: F[X])],
    )(using
      Applicative[G],
    ): G[H[Out]]
  }

  private object DistFImpl {
    case class Single[F[_], Lbl <: String, A](
      label: Lbl,
    ) extends DistFImpl[F, Lbl :: A] {
      override type Out = Lbl :: F[A]
      override def operationalize(f: Focus[**, F]): Operationalized[F, Lbl :: A]{type Out = Lbl :: F[A]} =
        f match
          case Focus.Id() =>
            Id[Lbl :: A]()
          case f: Focus.Fst[pr, f1, b] =>
            val d1: Operationalized[f1, Lbl :: A]{type Out = Lbl :: f1[A]} =
              Single[f1, Lbl, A](label).operationalize(f.i)
            DistSnd[f1, b, Lbl :: A, Lbl :: f1[A], Lbl :: F[A]](d1, DistRLImpl.Single(label))
          case f: Focus.Snd[pr, f2, a] =>
            val d2: Operationalized[f2, Lbl :: A]{type Out = Lbl :: f2[A]} =
              Single[f2, Lbl, A](label).operationalize(f.i)
            DistFst[a, f2, Lbl :: A, Lbl :: f2[A], Lbl :: F[A]](d2, DistLRImpl.Single(label))

      override def foldA[G[_], H[_]](
        mapA: [LblX, X] => Injector[LblX, X, Lbl :: A] => G[H[LblX :: F[X]]],
        snoc: [FInit, LblX, X] => (init: H[FInit], last: H[LblX :: F[X]]) => H[FInit || LblX :: F[X]],
      )(using
      Applicative[G],
    ): G[H[Out]] =
        mapA(Member.Single(label))
    }

    case class Snoc[F[_], Init, Lbl <: String, A, FInit](
      init: DistFImpl[F, Init] { type Out = FInit },
      lbl: Lbl,
    ) extends DistFImpl[F, Init || (Lbl :: A)] {
      override type Out = FInit || (Lbl :: F[A])
      override def operationalize(f: Focus[**, F]): Operationalized[F, Init || (Lbl :: A)]{type Out = FInit || (Lbl :: F[A])} =
        init.operationalize(f).extend[Lbl, A](lbl)

      override def foldA[G[_], H[_]](
        mapA: [LblX, X] => Injector[LblX, X, Init || Lbl :: A] => G[H[LblX :: F[X]]],
        snoc: [FInit, LblX, X] => (init: H[FInit], last: H[LblX :: F[X]]) => H[FInit || LblX :: F[X]],
      )(using
        G: Applicative[G],
      ): G[H[Out]] = {
        val mapAInit: [LblX, X] => Injector[LblX, X, Init] => G[H[LblX :: F[X]]] =
          [LblX, X] => (i: Injector[LblX, X, Init]) => mapA[LblX, X](i.inInit)

        val hLast: G[H[Lbl :: F[A]]] = mapA(Member.InLast(lbl))
        val hInit: G[H[FInit]]       = init.foldA(mapAInit, snoc)
        G.map2(hInit, hLast)(snoc(_, _))
      }
    }

    /** Like [[DistFImpl]], witnesses that distributing `F` into `Cases` yields `Out`.
     *  Unlike [[DistFImpl]], [[Operationalized]] is defined by induction over the structure of `F`
     *  (as opposed to by induction over `Cases`). As such, it can be more readily used
     *  to generate the distributing function `F[OneOf[Cases]] -> OneOf[Out]`.
     */
    sealed trait Operationalized[F[_], Cases] { self =>
      type Out
      def extend[Lbl <: String, B](lbl: Lbl): Operationalized[F, Cases || (Lbl :: B)]{type Out = self.Out || (Lbl :: F[B])}
      def compile: F[Enum[Cases]] -> Enum[Out]
    }

    case class Id[Cases]() extends DistFImpl.Operationalized[[x] =>> x, Cases] {
      override type Out = Cases
      override def extend[ZLbl <: String, Z](zLbl: ZLbl): Operationalized[[x] =>> x, Cases || (ZLbl :: Z)]{type Out = Cases || (ZLbl :: Z)} =
        Id[Cases || (ZLbl :: Z)]()
      override def compile: Enum[Cases] -> Enum[Cases] =
        cat.id[Enum[Cases]]
    }

    case class DistFst[A, F2[_], Cases, F2Cases, Res](
      distF2: DistFImpl.Operationalized[F2, Cases] { type Out = F2Cases },
      dist1: DistLRImpl[A, F2Cases] { type Out = Res },
    ) extends DistFImpl.Operationalized[[x] =>> A ** F2[x], Cases] {
      override type Out = Res
      override def extend[Lbl <: String, Z](lbl: Lbl): Operationalized[[x] =>> A ** F2[x], Cases || (Lbl :: Z)]{type Out = Res || (Lbl :: (A ** F2[Z]))} =
        val inner: Operationalized[F2, Cases || (Lbl :: Z)]{type Out = F2Cases || (Lbl :: F2[Z])} =
          distF2.extend[Lbl, Z](lbl)
        val outer: DistLRImpl[A, F2Cases || (Lbl :: F2[Z])]{type Out = Res || (Lbl :: (A ** F2[Z]))} =
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
          dist1.compile,
        )
    }

    case class DistSnd[F1[_], B, Cases, F1Cases, Res](
      distF1: DistFImpl.Operationalized[F1, Cases] { type Out = F1Cases },
      dist2: DistRLImpl[B, F1Cases] { type Out = Res },
    ) extends DistFImpl.Operationalized[[x] =>> F1[x] ** B, Cases] {
      override type Out = Res
      override def extend[Lbl <: String, Z](lbl: Lbl): Operationalized[[x] =>> F1[x] ** B, Cases || (Lbl :: Z)]{type Out = Res || (Lbl :: (F1[Z] ** B))} =
        val inner: Operationalized[F1, Cases || (Lbl :: Z)]{type Out = F1Cases || (Lbl :: F1[Z])} =
          distF1.extend[Lbl, Z](lbl)
        val outer: DistRLImpl[B, F1Cases || (Lbl :: F1[Z])]{type Out = Res || (Lbl :: (F1[Z] ** B))} =
          dist2.extend[Lbl, F1[Z]](lbl)
        DistSnd(inner, outer)
      override def compile: (F1[Enum[Cases]] ** B) -> Enum[Res] =
        import cat.{andThen, id, par}
        andThen(
          par(
            distF1.compile,
            id[B]
          ),
          dist2.compile
        )
    }

    def intoCases[F[_], Cases](cases: CaseList[Cases]): DistF[F, Cases] =
      cases match
        case s: CaseListImpl.SingleCaseList[lbl, a] =>
          DistFImpl.Single[F, lbl, a](s.lbl)
        case s: CaseListImpl.SnocCaseList[init, lbl, a] =>
          val init: DistF[F, init] = intoCases(s.init)
          DistFImpl.Snoc[F, init, lbl, a, init.Out](init, s.lbl)
  }

  private sealed trait HandlersBuilder[Cases, RemainingCases, R]
  private object HandlersBuilder {
    case class Empty[Cases, R]() extends HandlersBuilder[Cases, Cases, R]
    case class Snoc[Cases, Init, Lbl, Z, R](
      init: HandlersBuilder[Cases, Init || (Lbl :: Z), R],
      last: Z -> R,
    ) extends HandlersBuilder[Cases, Init, R]
    def addHandler[Cases, Init, Lbl, B, R](
      b: HandlersBuilder[Cases, Init || (Lbl :: B), R],
      h: B -> R,
    ): HandlersBuilder[Cases, Init, R] =
      Snoc(b, h)
    def build[Cases, Lbl, Z, R](
      b: HandlersBuilder[Cases, Lbl :: Z, R],
      h: Z -> R,
    ): HandlersImpl[Cases, R] =
      build[Cases, Lbl :: Z, R](b, HandlersImpl.Single(h))
    def build[Cases, Cases0, R](
      b: HandlersBuilder[Cases, Cases0, R],
      acc: HandlersImpl[Cases0, R],
    ): HandlersImpl[Cases, R] =
      b match
        case Empty()          => acc
        case Snoc(init, last) => build(init, HandlersImpl.Snoc(acc, last))
  }

  private sealed trait HandlersImpl[Cases, R] {
    def compile: Enum[Cases] -> R
    def asSingle[LblX, X](using Cases =:= (LblX :: X)): X -> R
  }

  private object HandlersImpl {
    case class Single[Lbl, A, R](h: A -> R) extends HandlersImpl[Lbl :: A, R] {
      override def compile: Enum[Lbl :: A] -> R =
        extract[Lbl, A] > h

      override def asSingle[LblX, X](using ev: Lbl :: A =:= LblX :: X): X -> R =
        ev match { case BiInjective[::](_, ev) => ev.substituteCo[[a] =>> a -> R](h) }
    }

    case class Snoc[Init, Lbl, Z, R](
      init: HandlersImpl[Init, R],
      last: Z -> R,
    ) extends HandlersImpl[Init || (Lbl :: Z), R] {
      override def compile: Enum[Init || (Lbl :: Z)] -> R =
        peel[Init, Lbl, Z] > either(init.compile, last)

      override def asSingle[LblX, X](using (Init || (Lbl :: Z)) =:= LblX :: X): X -> R =
        throw AssertionError(s"Impossible (A || B) =:= (C :: D), as || and :: are distinct class types.")
    }

    def snoc[Init, Lbl, Z, R](
      init: HandlersImpl[Init, R],
      last: HandlersImpl[Lbl :: Z, R]
    ): HandlersImpl[Init || Lbl :: Z, R] =
      Snoc(init, last.asSingle)

    def ofDist[F[_], Cases, R, G[_]](
      d: DistF[F, Cases],
      h: [X] => Injector[?, X, Cases] => G[F[X] -> R],
    )(using
      G: Applicative[G],
    ): G[Handlers[d.Out, R]] =
      d.foldA[G, HandlersImpl[_, R]](
        [LblX, X] => (i: Injector[LblX, X, Cases]) => h[X](i).map(HandlersImpl.Single(_)),
        [FInit, LblX, X] => (
          init: HandlersImpl[FInit, R],
          last: HandlersImpl[LblX :: F[X], R],
        ) =>
          HandlersImpl.snoc(init, last),
      )
  }

  private class PartitioningImpl[Cases](
    cases: CaseList[Cases],
  )(using
    BiInjective[||],
    BiInjective[::],
  ) extends libretto.lambda.Partitioning[->, **, Enum[Cases]] {
    override type Partition[A] =
      Injector[?, A, Cases]

    override def showPartition[A](p: Partition[A]): String =
      p.label

    override def reinject[P](p: Injector[?, P, Cases]): P -> Enum[Cases] =
      inj(p)

    override def isTotal[P](p: Injector[?, P, Cases]): Option[Enum[Cases] -> P] =
      libretto.lambda.UnhandledCase.raise("PartitioningImpl.isTotal")

    override def sameAs(
      that: libretto.lambda.Partitioning[->, **, Enum[Cases]],
    ): Option[TypeEqK[Injector[?, _, Cases], that.Partition]] =
      that match
        case that1: (PartitioningImpl[Cases] & that.type) =>
          Some(TypeEqK.refl[this.Partition]): Option[TypeEqK[this.Partition, that1.Partition]]
        case _ =>
          None

    override def samePartition[P, Q](
      p: Injector[?, P, Cases],
      q: Injector[?, Q, Cases],
    ): Option[P =:= Q] =
      p testEqual q

    override def compileAt[F[_], G[_], R](
      pos: Focus[**, F],
      handleAnyPartition: [X] => Partition[X] => G[F[X] -> R],
    )(using
      Applicative[G],
    ): G[F[Enum[Cases]] -> R] =
      val d: DistF[F, Cases] =
        DistFImpl.intoCases(cases)
      val handlers: G[Handlers[d.Out, R]] =
        HandlersImpl.ofDist(d, handleAnyPartition)
      handlers.map { handlers =>
        distF(using pos, d) > handle(handlers)
      }
  }
}
