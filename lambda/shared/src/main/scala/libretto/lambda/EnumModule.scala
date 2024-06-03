package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, StaticValue, TypeEq, TypeEqK}
import libretto.lambda.util.TypeEqK.Refl
import libretto.lambda.util.unapply.Unapply

class EnumModule[->[_, _], **[_, _], ++[_, _], Enum[_], ::[_, _], of[_, _]](
  inj: [Label, A, Cases] => EnumModule.Injector[::, of, Label, A, Cases] => (A -> Enum[Cases]),
  peel: [Label, A, Cases] => DummyImplicit ?=> Enum[(Label of A) :: Cases] -> (A ++ Enum[Cases]),
  unpeel: [Label, A, Cases] => DummyImplicit ?=> (A ++ Enum[Cases]) -> Enum[(Label of A) :: Cases],
  extract: [Label, A] => DummyImplicit ?=> Enum[Label of A] -> A,
)(
  cat: SemigroupalCategory[->, **],
  cocat: CocartesianSemigroupalCategory[->, ++],
  distr: Distribution[->, **, ++],
)(using
  BiInjective[::],
  BiInjective[of],
) {
  import EnumModule.*
  import cocat.{either, injectL, injectR}

  given SemigroupalCategory[->, **] = cat

  type Extractor[A, B] = libretto.lambda.Partitioning.Extractor[->, **, A, B]

  type Injector[Label, A, Cases] = EnumModule.Injector[::, of, Label, A, Cases]

  /** Witnesses that `Cases` is a list of cases, usable in `Enum`,
   * i.e. that `Cases` is of the form `(Name1 of T1) :: ... :: (NameN of TN)`.
   */
  opaque type CaseList[Cases] = CaseListImpl[Cases]

  opaque type IsCaseOf[Label, Cases] <: { type Type } = Injector[Label, ?, Cases]
  opaque type Handlers[Cases, R] = HandlersImpl[Cases, R]
  opaque type DistLR[A, Cases] = DistLRImpl[A, Cases]
  opaque type DistRL[B, Cases] = DistRLImpl[B, Cases]
  opaque type DistF[F[_], Cases] = DistFImpl[F, Cases]

  def inject[Cases](label: String)(using c: IsCaseOf[label.type, Cases]): c.Type -> Enum[Cases] =
    inj[label.type, c.Type, Cases](c)

  def make[ADT](using u: Unapply[ADT, Enum])(label: String)(using c: IsCaseOf[label.type, u.A]): c.Type -> ADT =
    inj[label.type, c.Type, u.A](c)
      .to(using u.ev.flip)

  def handle[Cases, R](handlers: Handlers[Cases, R]): Enum[Cases] -> R =
    handlers.compile

  def handle[ADT](using u: Unapply[ADT, Enum]): HandleInit[u.A] =
    HandleInit[u.A]

  class HandleInit[Cases]:
    def apply[R](handlers: Handlers.InitialBuilder[Cases] => Handlers[Cases, R]): Enum[Cases] -> R =
      handle[Cases, R](handlers(Handlers[Cases]))

  def distF[F[_], Cases](using F: Focus[**, F], ev: DistF[F, Cases]): F[Enum[Cases]] -> Enum[ev.Out] =
    distF(ev.operationalize(F))

  private def distF[F[_], Cases](ev: DistFImpl.Operationalized[F, Cases]): F[Enum[Cases]] -> Enum[ev.Out] =
    ev.compile

  def distLR[A, Cases](using ev: DistLR[A, Cases]): (A ** Enum[Cases]) -> Enum[ev.Out] =
    distLR_[A, Cases, ev.Out]

  private def distLR_[A, Cases, ACases](using ev: DistLR[A, Cases] { type Out = ACases }): (A ** Enum[Cases]) -> Enum[ACases] =
    ev match
      case s: DistLRImpl.Single[a, n, b] =>
        summon[Cases =:= (n of b)]
        val ev1: ((n of (A ** b)) =:= ACases) =
          summon[(n of (A ** b)) =:= s.Out] andThen summon[s.Out =:= ACases]
        distLRSingle(s.label).to(using ev1.liftCo[Enum])
      case c: DistLRImpl.Cons[a, n, h, t, at] =>
        val ev1: (((n of (a ** h)) :: at) =:= ACases) =
          summon[((n of (a ** h)) :: at) =:= c.Out] andThen summon[c.Out =:= ACases]
        distLRIntoTail[A, n, h, t, at](c.hLbl, c.tail).to(using ev1.liftCo[Enum])

  private def distLRSingle[A, Lbl <: String, B](
    lbl: Lbl,
  ): (A ** Enum[Lbl of B]) -> Enum[Lbl of (A ** B)] =
    extract[Lbl, B].inSnd[A] > inj(Injector.Single(lbl))

  private def distLRIntoTail[A, HLbl <: String, H, Tail, ATail](
    hLbl: HLbl,
    ev: DistLRImpl[A, Tail] { type Out = ATail },
  ): (A ** Enum[(HLbl of H) :: Tail]) -> Enum[(HLbl of (A ** H)) :: ATail] =
    cat.snd(peel[HLbl, H, Tail]) > distr.distLR > either(
      inj(Injector.InHead(hLbl)),
      distLR(using ev) > injectR > unpeel[HLbl, A ** H, ATail],
    )

  def distRL[B, Cases](using ev: DistRL[B, Cases]): (Enum[Cases] ** B) -> Enum[ev.Out] =
    distRL_[B, Cases, ev.Out]

  private def distRL_[B, Cases, BCases](using ev: DistRL[B, Cases] { type Out = BCases }): (Enum[Cases] ** B) -> Enum[BCases] =
    ev match
      case s: DistRLImpl.Single[b, n, a] =>
        val ev1: ((n of (a ** B)) =:= BCases) =
          summon[(n of (a ** B)) =:= s.Out] andThen summon[s.Out =:= BCases]
        distRLSingle(s.label).to(using ev1.liftCo[Enum])
      case c: DistRLImpl.Cons[b, n, h, t, bt] =>
        val ev1: (((n of (h ** b)) :: bt) =:= BCases) =
          summon[((n of (h ** b)) :: bt) =:= c.Out] andThen summon[c.Out =:= BCases]
        distRLIntoTail[B, n, h, t, bt](c.hLbl, c.tail).to(using ev1.liftCo[Enum])

  private def distRLSingle[B, Lbl <: String, A](
    lbl: Lbl,
  ): (Enum[Lbl of A] ** B) -> Enum[Lbl of (A ** B)] =
    extract[Lbl, A].inFst[B] > inj(Injector.Single(lbl))

  private def distRLIntoTail[B, HLbl <: String, H, Tail, BTail](
    hLbl: HLbl,
    ev: DistRLImpl[B, Tail] { type Out = BTail },
  ): (Enum[(HLbl of H) :: Tail] ** B) -> Enum[(HLbl of (H ** B)) :: BTail] =
    cat.fst(peel[HLbl, H, Tail]) > distr.distRL > either(
      inj(Injector.InHead(hLbl)),
      distRL(using ev) > injectR > unpeel[HLbl, H ** B, BTail],
    )

  given singleCaseList[Lbl <: String, A](using label: StaticValue[Lbl]): CaseList[Lbl of A] =
    CaseListImpl.singleCase(label.value)
  given consCaseList[HLbl <: String, H, Tail](using hLbl: StaticValue[HLbl], t: CaseList[Tail]): CaseList[(HLbl of H) :: Tail] =
    CaseListImpl.cons(hLbl.value, t)

  given singleInjector[Lbl <: String, A](using label: StaticValue[Lbl]): Injector[Lbl, A, Lbl of A] =
    Injector.Single(label.value)
  given headInjector[HLbl <: String, H, Tail](using hLbl: StaticValue[HLbl]): Injector[HLbl, H, (HLbl of H) :: Tail] =
    Injector.InHead(hLbl.value)
  given tailInjector[Lbl, A, HLbl, H, Tail](using j: Injector[Lbl, A, Tail]): Injector[Lbl, A, (HLbl of H) :: Tail] =
    Injector.InTail(j)

  given isSingleCase[Lbl <: String, A](using label: StaticValue[Lbl]): IsCaseOf[Lbl, Lbl of A] { type Type = A } =
    Injector.Single(label.value)
  given isHeadCase[HLbl <: String, H, Tail](using hLbl: StaticValue[HLbl]): IsCaseOf[HLbl, (HLbl of H) :: Tail] { type Type = H } =
    Injector.InHead(hLbl.value)
  given isTailInjector[Lbl, HLbl, H, Tail](using j: IsCaseOf[Lbl, Tail]): IsCaseOf[Lbl, (HLbl of H) :: Tail] { type Type = j.Type } =
    Injector.InTail(j)

  given distLRCons[A, Label <: String, H, Tail](using
    label: StaticValue[Label],
    tail: DistLR[A, Tail]
  ): DistLR[A, (Label of H) :: Tail] { type Out = (Label of (A ** H)) :: tail.Out } =
    DistLRImpl.cons[A, Label, H, Tail](label.value, tail)

  given distLRSingle[A, Label <: String, B](using
    label: StaticValue[Label],
  ): DistLR[A, Label of B] { type Out = Label of (A ** B) } =
    DistLRImpl.Single(label.value)

  given distFSingle[F[_], Lbl <: String, A](using label: StaticValue[Lbl]): DistF[F, Lbl of A]{ type Out = Lbl of F[A] } =
    DistFImpl.Single(label.value)
  given distFCons[F[_], Label <: String, H, Tail](using
    label: StaticValue[Label],
    tail: DistF[F, Tail],
  ): DistF[F, (Label of H) :: Tail] { type Out = (Label of F[H]) :: tail.Out } =
    DistFImpl.Cons(label.value, tail)

  object Handlers {
    def single[Lbl, A, R](h: A -> R): Handlers[Lbl of A, R] =
      HandlersImpl.Single(h)
    def cons[HLbl, H, T, R](
      h: H -> R,
      t: Handlers[T, R],
    ): Handlers[(HLbl of H) :: T, R] =
      HandlersImpl.Cons(h, t)

    def apply[Cases, R]: Builder[Cases, Cases, R] =
      HandlersBuilder.Empty()

    def apply[Cases]: InitialBuilder[Cases] =
      ()

    opaque type Builder[Cases, RemainingCases, R] =
      HandlersBuilder[Cases, RemainingCases, R]

    /** Compared to [[Builder]], defers specifying the result type. */
    opaque type InitialBuilder[Cases] =
      Unit

    extension [Cases, HLbl, H, T, R](b: Builder[Cases, (HLbl of H) :: T, R])
      def caseOf[Lbl](using StaticValue[Lbl], Lbl =:= HLbl)(h: H -> R): Builder[Cases, T, R] =
        HandlersBuilder.addHandler(b, h)

    extension [Cases, Lbl, A, R](b: Builder[Cases, Lbl of A, R])
      def caseOf[L](using StaticValue[L], L =:= Lbl, DummyImplicit)(h: A -> R): Handlers[Cases, R] =
        HandlersBuilder.build(b, h)

    extension [HLbl, H, T](b: InitialBuilder[(HLbl of H) :: T])
      def caseOf[Lbl](using StaticValue[Lbl], Lbl =:= HLbl): [R] => (H -> R) => Builder[(HLbl of H) :: T, T, R] =
        [R] => h => apply[(HLbl of H) :: T, R].caseOf[Lbl](h)

    extension [Lbl, A](b: InitialBuilder[Lbl of A])
      def caseOf[L](using StaticValue[L], L =:= Lbl, DummyImplicit): [R] => (A -> R) => Handlers[Lbl of A, R] =
       [R] => h => apply[Lbl of A, R].caseOf[L](h)
  }

  opaque type Partitioning[Cases] <: libretto.lambda.Partitioning[->, **, Enum[Cases]] =
    PartitioningImpl[Cases]

  def partitioning[Cases](using ev: CaseList[Cases]): Partitioning[Cases] =
    PartitioningImpl(ev)

  def partition[ADT](using
    u: Unapply[ADT, Enum],
    ev: CaseList[u.A],
  ): Partitioning[u.A] =
    partitioning[u.A]

  def caseExtractor[Cases, C](p: Partitioning[Cases], ev: IsCaseOf[C, Cases]): Extractor[Enum[Cases], ev.Type] =
    p.extractor[ev.Type](ev)

  private sealed trait CaseListImpl[Cases] {
    def distF[F[_]]: DistFImpl[F, Cases]
  }
  private object CaseListImpl {
    case class SingleCaseList[Lbl <: String, A](
      lbl: Lbl,
    ) extends CaseListImpl[Lbl of A] {
      override def distF[F[_]]: DistFImpl[F, Lbl of A] =
        DistFImpl.Single(lbl)
    }
    case class ConsCaseList[HLbl <: String, H, Tail](
      hLbl: HLbl,
      tail: CaseList[Tail],
    ) extends CaseListImpl[(HLbl of H) :: Tail] {
      override def distF[F[_]]: DistFImpl[F, (HLbl of H) :: Tail] =
        val ft = tail.distF[F]
        DistFImpl.Cons(hLbl, ft)
    }
    def singleCase[Lbl <: String, A](
      lbl: Lbl,
    ): CaseList[Lbl of A] =
      SingleCaseList(lbl)
    def cons[HLbl <: String, H, Tail](
      hLbl: HLbl,
      tail: CaseList[Tail],
    ): CaseList[(HLbl of H) :: Tail] =
      ConsCaseList(hLbl, tail)
  }

  private sealed trait DistLRImpl[A, Cases] { self =>
    type Out
    def extend[HLbl <: String, H](hLbl: HLbl): DistLRImpl[A, (HLbl of H) :: Cases]{type Out = (HLbl of (A ** H)) :: self.Out} =
      DistLRImpl.Cons(hLbl, this)
    def compile: (A ** Enum[Cases]) -> Enum[Out] =
      distLR(using this)
  }

  private object DistLRImpl {
    case class Single[A, Lbl <: String, B](label: Lbl) extends DistLRImpl[A, Lbl of B] {
      override type Out = Lbl of (A ** B)
    }
    case class Cons[A, HLbl <: String, H, Tail, ATail](
      hLbl: HLbl,
      tail: DistLRImpl[A, Tail] { type Out = ATail },
    ) extends DistLRImpl[A, (HLbl of H) :: Tail] {
      override type Out = (HLbl of (A ** H)) :: ATail
    }
    def cons[A, HLbl <: String, H, Tail](
      hLbl: HLbl,
      tail: DistLRImpl[A, Tail],
    ): DistLRImpl[A, (HLbl of H) :: Tail] { type Out = (HLbl of (A ** H)) :: tail.Out } =
      Cons[A, HLbl, H, Tail, tail.Out](hLbl, tail)
  }

  private sealed trait DistRLImpl[B, Cases] { self =>
    type Out
    def extend[HLbl <: String, H](hLbl: HLbl): DistRLImpl[B, (HLbl of H) :: Cases]{type Out = (HLbl of (H ** B)) :: self.Out} =
      DistRLImpl.Cons(hLbl, this)
    def compile: (Enum[Cases] ** B) -> Enum[Out] =
      distRL(using this)
  }

  private object DistRLImpl {
    case class Single[B, Lbl <: String, A](
      label: Lbl,
    ) extends DistRLImpl[B, Lbl of A] {
      override type Out = Lbl of (A ** B)
    }
    case class Cons[B, HLbl <: String, H, Tail, BTail](
      hLbl: HLbl,
      tail: DistRLImpl[B, Tail] { type Out = BTail },
    ) extends DistRLImpl[B, (HLbl of H) :: Tail] {
      override type Out = (HLbl of (H ** B)) :: BTail
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
    ) extends DistFImpl[F, Lbl of A] {
      override type Out = Lbl of F[A]
      override def operationalize(f: Focus[**, F]): Operationalized[F, Lbl of A]{type Out = Lbl of F[A]} =
        f match
          case Focus.Id() =>
            Id[Lbl of A]()
          case f: Focus.Fst[pr, f1, b] =>
            val d1: Operationalized[f1, Lbl of A]{type Out = Lbl of f1[A]} =
              Single[f1, Lbl, A](label).operationalize(f.i)
            DistSnd[f1, b, Lbl of A, Lbl of f1[A], Lbl of F[A]](d1, DistRLImpl.Single(label))
          case f: Focus.Snd[pr, f2, a] =>
            val d2: Operationalized[f2, Lbl of A]{type Out = Lbl of f2[A]} =
              Single[f2, Lbl, A](label).operationalize(f.i)
            DistFst[a, f2, Lbl of A, Lbl of f2[A], Lbl of F[A]](d2, DistLRImpl.Single(label))
      override def handlers[G[_], R](
        h: [X] => Injector[?, X, Lbl of A] => G[F[X] -> R],
      )(using
        G: Applicative[G],
      ): G[HandlersImpl[Lbl of F[A], R]] =
        h(Injector.Single(label))
          .map(HandlersImpl.Single(_))
    }

    case class Cons[F[_], HLbl <: String, H, Tail, FTail](
      hLbl: HLbl,
      tail: DistFImpl[F, Tail] { type Out = FTail },
    ) extends DistFImpl[F, (HLbl of H) :: Tail] {
      override type Out = (HLbl of F[H]) :: FTail
      override def operationalize(f: Focus[**, F]): Operationalized[F, (HLbl of H) :: Tail]{type Out = (HLbl of F[H]) :: FTail} =
        tail.operationalize(f).extend[HLbl, H](hLbl)
      override def handlers[G[_], R](
        h: [X] => Injector[?, X, (HLbl of H) :: Tail] => G[F[X] -> R],
      )(using
        G: Applicative[G],
      ): G[HandlersImpl[(HLbl of F[H]) :: FTail, R]] =
        val h0: G[F[H] -> R] =
          h[H](Injector.InHead(hLbl))
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
      def extend[HLbl <: String, H](hLbl: HLbl): Operationalized[F, (HLbl of H) :: Cases]{type Out = (HLbl of F[H]) :: self.Out}
      def compile: F[Enum[Cases]] -> Enum[Out]
    }

    case class Id[Cases]() extends DistFImpl.Operationalized[[x] =>> x, Cases] {
      override type Out = Cases
      override def extend[HLbl <: String, H](hLbl: HLbl): Operationalized[[x] =>> x, (HLbl of H) :: Cases]{type Out = (HLbl of H) :: Cases} =
        Id[(HLbl of H) :: Cases]()
      override def compile: Enum[Cases] -> Enum[Cases] =
        cat.id[Enum[Cases]]
    }

    case class DistFst[A, F2[_], Cases, F2Cases, Res](
      distF2: DistFImpl.Operationalized[F2, Cases] { type Out = F2Cases },
      dist1: DistLRImpl[A, F2Cases] { type Out = Res },
    ) extends DistFImpl.Operationalized[[x] =>> A ** F2[x], Cases] {
      override type Out = Res
      override def extend[HLbl <: String, H](hLbl: HLbl): Operationalized[[x] =>> A ** F2[x], (HLbl of H) :: Cases]{type Out = (HLbl of (A ** F2[H])) :: Res} =
        val inner: Operationalized[F2, (HLbl of H) :: Cases]{type Out = (HLbl of F2[H]) :: F2Cases} =
          distF2.extend[HLbl, H](hLbl)
        val outer: DistLRImpl[A, (HLbl of F2[H]) :: F2Cases]{type Out = (HLbl of (A ** F2[H])) :: Res} =
          dist1.extend[HLbl, F2[H]](hLbl)
        DistFst[A, F2, (HLbl of H) :: Cases, (HLbl of F2[H]) :: F2Cases, (HLbl of (A ** F2[H])) :: Res](
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
      override def extend[HLbl <: String, H](hLbl: HLbl): Operationalized[[x] =>> F1[x] ** B, (HLbl of H) :: Cases]{type Out = (HLbl of (F1[H] ** B)) :: Res} =
        val inner: Operationalized[F1, (HLbl of H) :: Cases]{type Out = (HLbl of F1[H]) :: F1Cases} =
          distF1.extend[HLbl, H](hLbl)
        val outer: DistRLImpl[B, (HLbl of F1[H]) :: F1Cases]{type Out = (HLbl of (F1[H] ** B)) :: Res} =
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
      init: HandlersBuilder[Cases, (HLbl of H) :: T, R],
      last: H -> R,
    ) extends HandlersBuilder[Cases, T, R]
    def addHandler[Cases, HLbl, H, T, R](
      b: HandlersBuilder[Cases, (HLbl of H) :: T, R],
      h: H -> R,
    ): HandlersBuilder[Cases, T, R] =
      Snoc(b, h)
    def build[Cases, Lbl, Z, R](
      b: HandlersBuilder[Cases, Lbl of Z, R],
      h: Z -> R,
    ): HandlersImpl[Cases, R] =
      build[Cases, Lbl of Z, R](b, HandlersImpl.Single(h))
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
    case class Single[Lbl, A, R](h: A -> R) extends HandlersImpl[Lbl of A, R] {
      override def compile: Enum[Lbl of A] -> R =
        extract[Lbl, A] > h
    }
    case class Cons[HLbl, H, T, R](
      head: H -> R,
      tail: HandlersImpl[T, R],
    ) extends HandlersImpl[(HLbl of H) :: T, R] {
      override def compile: Enum[(HLbl of H) :: T] -> R =
        peel[HLbl, H, T] > either(head, tail.compile)
    }
  }

  private class PartitioningImpl[Cases](
    cases: CaseList[Cases],
  )(using
    BiInjective[::],
    BiInjective[of],
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
      handle: [X] => Partition[X] => G[F[X] -> R],
    )(using
      Applicative[G],
    ): G[F[Enum[Cases]] -> R] =
      val d: DistF[F, Cases] =
        cases.distF[F]
      val handlers: G[Handlers[d.Out, R]] =
        d.handlers[G, R](handle)
      handlers.map { handlers =>
        distF(using pos, d) > EnumModule.this.handle(handlers)
      }
  }
}

object EnumModule {
  sealed trait Injector[::[_, _], of[_, _], Label, A, Cases] {
    import Injector.*

    final type Type = A

    def label: Label & String

    def inTail[HLbl, H]: Injector[::, of, Label, A, (HLbl of H) :: Cases] =
      InTail(this)

    infix def testEqual[Lbl2, B](that: Injector[::, of, Lbl2, B, Cases])(using BiInjective[::],  BiInjective[of]): Option[A =:= B]

    protected def testEqualToSingle[Lbl2, B](using Cases =:= (Lbl2 of B), BiInjective[of]): Option[A =:= B]

    protected def testEqualToInHead[Lbl2, B, T](using Cases =:= ((Lbl2 of B) :: T), BiInjective[::], BiInjective[of]): Option[A =:= B]
  }

  object Injector {
    case class InHead[::[_, _], of[_, _], Label <: String, A, Tail](
      label: Label,
    ) extends Injector[::, of, Label, A, (Label of A) :: Tail]:
      override def testEqual[Lbl2, B](that: Injector[::, of, Lbl2, B, of[Label, A] :: Tail])(using BiInjective[::], BiInjective[of]): Option[A =:= B] =
        that.testEqualToInHead[Label, A, Tail].map(_.flip)

      override protected def testEqualToInHead[Lbl2, B, T](using
        ev: (Label of A) :: Tail =:= (Lbl2 of B) :: T,
        i: BiInjective[::],
        j: BiInjective[of],
      ): Option[A =:= B] =
        ev match { case BiInjective[::](BiInjective[of](_, ev1), _) => Some(ev1) }

      override protected def testEqualToSingle[Lbl2, B](using of[Label, A] :: Tail =:= of[Lbl2, B], BiInjective[of]): Option[A =:= B] =
        None

    case class Single[::[_, _], of[_, _], Label <: String, A](
      label: Label,
    ) extends Injector[::, of, Label, A, Label of A]:
      override def testEqual[Lbl2, B](that: Injector[::, of, Lbl2, B, Label of A])(using BiInjective[::], BiInjective[of]): Option[A =:= B] =
        that.testEqualToSingle[Label, A].map(_.flip)

      override protected def testEqualToSingle[Lbl2, B](using
        ev: (Label of A) =:= (Lbl2 of B),
        inj: BiInjective[of],
      ): Option[A =:= B] =
        ev match { case BiInjective[of](_, ev1) => Some(ev1) }

      override protected def testEqualToInHead[Lbl2, B, T](using of[Label, A] =:= of[Lbl2, B] :: T, BiInjective[::], BiInjective[of]): Option[A =:= B] =
        None

    case class InTail[::[_, _], of[_, _], Label, A, HLbl, H, Tail](
      i: Injector[::, of, Label, A, Tail],
    ) extends Injector[::, of, Label, A, (HLbl of H) :: Tail]:
      override def label: Label & String = i.label

      override def testEqual[Lbl2, B](
        that: Injector[::, of, Lbl2, B, (HLbl of H) :: Tail],
      )(using
        BiInjective[::],
        BiInjective[of],
      ): Option[A =:= B] =
        that match
          case InTail(j) => i testEqual j
          case _ => None

      override protected def testEqualToSingle[Lbl2, B](using of[HLbl, H] :: Tail =:= of[Lbl2, B], BiInjective[of]): Option[A =:= B] =
        None

      override protected def testEqualToInHead[Lbl2, B, T](using of[HLbl, H] :: Tail =:= of[Lbl2, B] :: T, BiInjective[::], BiInjective[of]): Option[A =:= B] =
        None
  }
}
