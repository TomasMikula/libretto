package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, StaticValue, TypeEq, TypeEqK}
import libretto.lambda.util.TypeEqK.Refl
import libretto.lambda.util.unapply.Unapply

trait EnumModule[->[_, _], **[_, _], Enum[_], ||[_, _], ::[_, _]] {
  import EnumModule.*

  /** Witnesses that `Cases` is a list :: cases, usable in `Enum`,
   * i.e. that `Cases` is :: the form `(Name1 :: T1) || ... || (NameN :: TN)`.
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
  given consCaseList[HLbl <: String, H, Tail](using hLbl: StaticValue[HLbl], t: CaseList[Tail]): CaseList[(HLbl :: H) || Tail]

  given isSingleCase[Lbl <: String, A](using label: StaticValue[Lbl]): (IsCaseOf[Lbl, Lbl :: A] with { type Type = A })
  given isHeadCase[HLbl <: String, H, Tail](using hLbl: StaticValue[HLbl]): (IsCaseOf[HLbl, (HLbl :: H) || Tail] with { type Type = H })
  given isTailCase[Lbl, HLbl, H, Tail](using j: IsCaseOf[Lbl, Tail]): (IsCaseOf[Lbl, (HLbl :: H) || Tail] with { type Type = j.Type })

  given distLRCons[A, Label <: String, H, Tail](using
    label: StaticValue[Label],
    tail: DistLR[A, Tail]
  ): (DistLR[A, (Label :: H) || Tail] with { type Out = (Label :: (A ** H)) || tail.Out })

  given distLRSingle[A, Label <: String, B](using
    label: StaticValue[Label],
  ): (DistLR[A, Label :: B] with { type Out = Label :: (A ** B) })

  given distFSingle[F[_], Lbl <: String, A](using label: StaticValue[Lbl]): (DistF[F, Lbl :: A] with { type Out = Lbl :: F[A] })

  given distFCons[F[_], Label <: String, H, Tail](using
    label: StaticValue[Label],
    tail: DistF[F, Tail],
  ): (DistF[F, (Label :: H) || Tail] with { type Out = (Label :: F[H]) || tail.Out })

  val Handlers: HandlersModule

  trait HandlersModule {
    type Builder[Cases, RemainingCases, R]

    def single[Lbl, A, R](h: A -> R): Handlers[Lbl :: A, R]

    def cons[HLbl, H, T, R](
      h: H -> R,
      t: Handlers[T, R],
    ): Handlers[(HLbl :: H) || T, R]

    def apply[Cases, R]: Builder[Cases, Cases, R]

    def apply[Cases]: InitialBuilder[Cases] =
      ()

    /** Compared to [[Builder]], defers specifying the result type. */
    opaque type InitialBuilder[Cases] =
      Unit

    extension [Cases, HLbl, H, T, R](b: Builder[Cases, (HLbl :: H) || T, R])
      def caseOf[Lbl](using StaticValue[Lbl], Lbl =:= HLbl)(h: H -> R): Builder[Cases, T, R]

    extension [Cases, Lbl, A, R](b: Builder[Cases, Lbl :: A, R])
      def caseOf[L](using StaticValue[L], L =:= Lbl, DummyImplicit)(h: A -> R): Handlers[Cases, R]

    extension [HLbl, H, T](b: InitialBuilder[(HLbl :: H) || T])
      def caseOf[Lbl](using StaticValue[Lbl], Lbl =:= HLbl): [R] => (H -> R) => Builder[(HLbl :: H) || T, T, R] =
        [R] => h => apply[(HLbl :: H) || T, R].caseOf[Lbl](h)

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
  type LeftAssociative[->[_, _], **[_, _], Enum[_], ||[_, _], ::[_, _]] =
    EnumModule[->, **, Enum, [c1, c2] =>> c2 || c1, ::]

  def fromBinarySums[->[_, _], **[_, _], ++[_, _], Enum[_], ||[_, _], ::[_, _]](
    inj: [Label, A, Cases] => Member[||, ::, Label, A, Cases] => (A -> Enum[Cases]),
    peel: [Label, A, Cases] => DummyImplicit ?=> Enum[(Label :: A) || Cases] -> (A ++ Enum[Cases]),
    unpeel: [Label, A, Cases] => DummyImplicit ?=> (A ++ Enum[Cases]) -> Enum[(Label :: A) || Cases],
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
  peel: [Label, A, Cases] => DummyImplicit ?=> Enum[(Label :: A) || Cases] -> (A ++ Enum[Cases]),
  unpeel: [Label, A, Cases] => DummyImplicit ?=> (A ++ Enum[Cases]) -> Enum[(Label :: A) || Cases],
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
  override given consCaseList[HLbl <: String, H, Tail](using hLbl: StaticValue[HLbl], t: CaseList[Tail]): CaseList[(HLbl :: H) || Tail] =
    CaseListImpl.cons(hLbl.value, t)

  override given isSingleCase[Lbl <: String, A](using label: StaticValue[Lbl]): (IsCaseOf[Lbl, Lbl :: A] with { type Type = A }) =
    Member.Single(label.value)
  override given isHeadCase[HLbl <: String, H, Tail](using hLbl: StaticValue[HLbl]): (IsCaseOf[HLbl, (HLbl :: H) || Tail] with { type Type = H }) =
    Member.InHead(hLbl.value)
  override given isTailCase[Lbl, HLbl, H, Tail](using j: IsCaseOf[Lbl, Tail]): (IsCaseOf[Lbl, (HLbl :: H) || Tail] with { type Type = j.Type }) =
    Member.InTail(j)

  override given distLRCons[A, Label <: String, H, Tail](using
    label: StaticValue[Label],
    tail: DistLR[A, Tail]
  ): (DistLR[A, (Label :: H) || Tail] with { type Out = (Label :: (A ** H)) || tail.Out }) =
    DistLRImpl.cons[A, Label, H, Tail](label.value, tail)

  override given distLRSingle[A, Label <: String, B](using
    label: StaticValue[Label],
  ): (DistLR[A, Label :: B] with { type Out = Label :: (A ** B) }) =
    DistLRImpl.Single(label.value)

  override given distFSingle[F[_], Lbl <: String, A](using label: StaticValue[Lbl]): (DistF[F, Lbl :: A] with { type Out = Lbl :: F[A] }) =
    DistFImpl.Single(label.value)
  override given distFCons[F[_], Label <: String, H, Tail](using
    label: StaticValue[Label],
    tail: DistF[F, Tail],
  ): (DistF[F, (Label :: H) || Tail] with { type Out = (Label :: F[H]) || tail.Out }) =
    DistFImpl.Cons(label.value, tail)

  override object Handlers extends HandlersModule {

    override opaque type Builder[Cases, RemainingCases, R] =
      HandlersBuilder[Cases, RemainingCases, R]

    override def single[Lbl, A, R](h: A -> R): Handlers[Lbl :: A, R] =
      HandlersImpl.Single(h)

    override def cons[HLbl, H, T, R](
      h: H -> R,
      t: Handlers[T, R],
    ): Handlers[(HLbl :: H) || T, R] =
      HandlersImpl.Cons(h, t)

    override def apply[Cases, R]: Builder[Cases, Cases, R] =
      HandlersBuilder.Empty()

    extension [Cases, HLbl, H, T, R](b: Builder[Cases, (HLbl :: H) || T, R])
      def caseOf[Lbl](using StaticValue[Lbl], Lbl =:= HLbl)(h: H -> R): Builder[Cases, T, R] =
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

  private sealed trait CaseListImpl[Cases] {
    def distF[F[_]]: DistFImpl[F, Cases]
  }
  private object CaseListImpl {
    case class SingleCaseList[Lbl <: String, A](
      lbl: Lbl,
    ) extends CaseListImpl[Lbl :: A] {
      override def distF[F[_]]: DistFImpl[F, Lbl :: A] =
        DistFImpl.Single(lbl)
    }
    case class ConsCaseList[HLbl <: String, H, Tail](
      hLbl: HLbl,
      tail: CaseList[Tail],
    ) extends CaseListImpl[(HLbl :: H) || Tail] {
      override def distF[F[_]]: DistFImpl[F, (HLbl :: H) || Tail] =
        val ft = tail.distF[F]
        DistFImpl.Cons(hLbl, ft)
    }
    def singleCase[Lbl <: String, A](
      lbl: Lbl,
    ): CaseList[Lbl :: A] =
      SingleCaseList(lbl)
    def cons[HLbl <: String, H, Tail](
      hLbl: HLbl,
      tail: CaseList[Tail],
    ): CaseList[(HLbl :: H) || Tail] =
      ConsCaseList(hLbl, tail)
  }

  private sealed trait DistLRImpl[A, Cases] { self =>
    type Out

    def compile: (A ** Enum[Cases]) -> Enum[Out]

    def extend[HLbl <: String, H](hLbl: HLbl): DistLRImpl[A, (HLbl :: H) || Cases]{type Out = (HLbl :: (A ** H)) || self.Out} =
      DistLRImpl.Cons(hLbl, this)
  }

  private object DistLRImpl {
    case class Single[A, Lbl <: String, B](label: Lbl) extends DistLRImpl[A, Lbl :: B] {
      override type Out = Lbl :: (A ** B)

      override def compile: (A ** Enum[Lbl :: B]) -> Enum[Out] =
        extract[Lbl, B].inSnd[A] > inj(Member.Single(label))
    }

    case class Cons[A, HLbl <: String, H, Tail, ATail](
      hLbl: HLbl,
      tail: DistLRImpl[A, Tail] { type Out = ATail },
    ) extends DistLRImpl[A, (HLbl :: H) || Tail] {
      override type Out = (HLbl :: (A ** H)) || ATail

      override def compile: (A ** Enum[(HLbl :: H) || Tail]) -> Enum[Out] =
        cat.snd(peel[HLbl, H, Tail]) > distr.distLR > either(
          inj(Member.InHead(hLbl)),
          tail.compile > injectR > unpeel[HLbl, A ** H, ATail],
        )
    }

    def cons[A, HLbl <: String, H, Tail](
      hLbl: HLbl,
      tail: DistLRImpl[A, Tail],
    ): DistLRImpl[A, (HLbl :: H) || Tail] { type Out = (HLbl :: (A ** H)) || tail.Out } =
      Cons[A, HLbl, H, Tail, tail.Out](hLbl, tail)
  }

  private sealed trait DistRLImpl[B, Cases] { self =>
    type Out

    def compile: (Enum[Cases] ** B) -> Enum[Out]

    def extend[HLbl <: String, H](hLbl: HLbl): DistRLImpl[B, (HLbl :: H) || Cases]{type Out = (HLbl :: (H ** B)) || self.Out} =
      DistRLImpl.Cons(hLbl, this)
  }

  private object DistRLImpl {
    case class Single[B, Lbl <: String, A](
      label: Lbl,
    ) extends DistRLImpl[B, Lbl :: A] {
      override type Out = Lbl :: (A ** B)

      override def compile: (Enum[Lbl :: A] ** B) -> Enum[Out] =
        extract[Lbl, A].inFst[B] > inj(Member.Single(label))
    }

    case class Cons[B, HLbl <: String, H, Tail, BTail](
      hLbl: HLbl,
      tail: DistRLImpl[B, Tail] { type Out = BTail },
    ) extends DistRLImpl[B, (HLbl :: H) || Tail] {
      override type Out = (HLbl :: (H ** B)) || BTail

      override def compile: (Enum[(HLbl :: H) || Tail] ** B) -> Enum[Out] =
        cat.fst(peel[HLbl, H, Tail]) > distr.distRL > either(
          inj(Member.InHead(hLbl)),
          tail.compile > injectR > unpeel[HLbl, H ** B, BTail],
        )
    }
  }

  private sealed trait DistFImpl[F[_], Cases] {
    type Out
    def operationalize(f: Focus[**, F]): DistFImpl.Operationalized[F, Cases] { type Out = DistFImpl.this.Out }
    def handlers[G[_], R](
      h: [X] => Injector[?, X, Cases] => G[F[X] -> R],
    )(using
      G: Applicative[G],
    ): G[Handlers[Out, R]]
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
      override def handlers[G[_], R](
        h: [X] => Injector[?, X, Lbl :: A] => G[F[X] -> R],
      )(using
        G: Applicative[G],
      ): G[HandlersImpl[Lbl :: F[A], R]] =
        h(Member.Single(label))
          .map(HandlersImpl.Single(_))
    }

    case class Cons[F[_], HLbl <: String, H, Tail, FTail](
      hLbl: HLbl,
      tail: DistFImpl[F, Tail] { type Out = FTail },
    ) extends DistFImpl[F, (HLbl :: H) || Tail] {
      override type Out = (HLbl :: F[H]) || FTail
      override def operationalize(f: Focus[**, F]): Operationalized[F, (HLbl :: H) || Tail]{type Out = (HLbl :: F[H]) || FTail} =
        tail.operationalize(f).extend[HLbl, H](hLbl)
      override def handlers[G[_], R](
        h: [X] => Injector[?, X, (HLbl :: H) || Tail] => G[F[X] -> R],
      )(using
        G: Applicative[G],
      ): G[HandlersImpl[(HLbl :: F[H]) || FTail, R]] =
        val h0: G[F[H] -> R] =
          h[H](Member.InHead(hLbl))
        val ht: [X] => Injector[?, X, Tail] => G[F[X] -> R] =
          [X] => (i: Injector[?, X, Tail]) =>
            h[X](i.inTail)
        G.map2(h0, tail.handlers(ht))(HandlersImpl.Cons(_, _))
    }

    /** Like [[DistFImpl]], witnesses that distributing `F` into `Cases` yields `Out`.
     *  Unlike [[DistFImpl]], [[Operationalized]] is defined by induction over the structure of `F`
     *  (as opposed to by induction over `Cases`). As such, it can be more readily used
     *  to generate the distributing function `F[OneOf[Cases]] -> OneOf[Out]`.
     */
    sealed trait Operationalized[F[_], Cases] { self =>
      type Out
      def extend[HLbl <: String, H](hLbl: HLbl): Operationalized[F, (HLbl :: H) || Cases]{type Out = (HLbl :: F[H]) || self.Out}
      def compile: F[Enum[Cases]] -> Enum[Out]
    }

    case class Id[Cases]() extends DistFImpl.Operationalized[[x] =>> x, Cases] {
      override type Out = Cases
      override def extend[HLbl <: String, H](hLbl: HLbl): Operationalized[[x] =>> x, (HLbl :: H) || Cases]{type Out = (HLbl :: H) || Cases} =
        Id[(HLbl :: H) || Cases]()
      override def compile: Enum[Cases] -> Enum[Cases] =
        cat.id[Enum[Cases]]
    }

    case class DistFst[A, F2[_], Cases, F2Cases, Res](
      distF2: DistFImpl.Operationalized[F2, Cases] { type Out = F2Cases },
      dist1: DistLRImpl[A, F2Cases] { type Out = Res },
    ) extends DistFImpl.Operationalized[[x] =>> A ** F2[x], Cases] {
      override type Out = Res
      override def extend[HLbl <: String, H](hLbl: HLbl): Operationalized[[x] =>> A ** F2[x], (HLbl :: H) || Cases]{type Out = (HLbl :: (A ** F2[H])) || Res} =
        val inner: Operationalized[F2, (HLbl :: H) || Cases]{type Out = (HLbl :: F2[H]) || F2Cases} =
          distF2.extend[HLbl, H](hLbl)
        val outer: DistLRImpl[A, (HLbl :: F2[H]) || F2Cases]{type Out = (HLbl :: (A ** F2[H])) || Res} =
          dist1.extend[HLbl, F2[H]](hLbl)
        DistFst[A, F2, (HLbl :: H) || Cases, (HLbl :: F2[H]) || F2Cases, (HLbl :: (A ** F2[H])) || Res](
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
      override def extend[HLbl <: String, H](hLbl: HLbl): Operationalized[[x] =>> F1[x] ** B, (HLbl :: H) || Cases]{type Out = (HLbl :: (F1[H] ** B)) || Res} =
        val inner: Operationalized[F1, (HLbl :: H) || Cases]{type Out = (HLbl :: F1[H]) || F1Cases} =
          distF1.extend[HLbl, H](hLbl)
        val outer: DistRLImpl[B, (HLbl :: F1[H]) || F1Cases]{type Out = (HLbl :: (F1[H] ** B)) || Res} =
          dist2.extend[HLbl, F1[H]](hLbl)
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
  }

  private sealed trait HandlersBuilder[Cases, RemainingCases, R]
  private object HandlersBuilder {
    case class Empty[Cases, R]() extends HandlersBuilder[Cases, Cases, R]
    case class Snoc[Cases, HLbl, H, T, R](
      init: HandlersBuilder[Cases, (HLbl :: H) || T, R],
      last: H -> R,
    ) extends HandlersBuilder[Cases, T, R]
    def addHandler[Cases, HLbl, H, T, R](
      b: HandlersBuilder[Cases, (HLbl :: H) || T, R],
      h: H -> R,
    ): HandlersBuilder[Cases, T, R] =
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
        case Snoc(init, last) => build(init, HandlersImpl.Cons(last, acc))
  }

  private sealed trait HandlersImpl[Cases, R] {
    def compile: Enum[Cases] -> R
  }

  private object HandlersImpl {
    case class Single[Lbl, A, R](h: A -> R) extends HandlersImpl[Lbl :: A, R] {
      override def compile: Enum[Lbl :: A] -> R =
        extract[Lbl, A] > h
    }
    case class Cons[HLbl, H, T, R](
      head: H -> R,
      tail: HandlersImpl[T, R],
    ) extends HandlersImpl[(HLbl :: H) || T, R] {
      override def compile: Enum[(HLbl :: H) || T] -> R =
        peel[HLbl, H, T] > either(head, tail.compile)
    }
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
        cases.distF[F]
      val handlers: G[Handlers[d.Out, R]] =
        d.handlers[G, R](handleAnyPartition)
      handlers.map { handlers =>
        distF(using pos, d) > handle(handlers)
      }
  }
}
