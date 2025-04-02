package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, SingletonType, TypeEq, TypeEqK}
import libretto.lambda.util.TypeEqK.Refl
import libretto.lambda.util.unapply.Unapply

trait EnumModule[->[_, _], **[_, _], Enum[_], ||[_, _], ::[_, _]] {
  import EnumModule.*

  val distr: DistributionNAry[->, **, Enum, ||, ::]

  /** Witnesses that `Cases` is a list of cases, usable in `Enum`,
   * i.e. that `Cases` is of the form `(Name1 :: T1) || ... || (NameN :: TN)`.
   */
  type CaseList[Cases] = ItemList[||, ::, Cases]

  type IsCaseOf[Label, Cases] <: AnyRef with { type Type }
  type EnumPartition[Cases, P]
  type Handlers[Cases, R]

  type DistF[F[_], Cases] = distr.DistF[F, Cases]
  type DistLR[A, Cases] = DistF[[x] =>> A ** x, Cases]
  type DistRL[B, Cases] = DistF[[x] =>> x ** B, Cases]

  def inject[Lbl, Cases](c: IsCaseOf[Lbl, Cases]): c.Type -> Enum[Cases]

  def inject[Cases](label: String)(using c: IsCaseOf[label.type, Cases]): c.Type -> Enum[Cases] =
    inject[label.type, Cases](c)

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

  given isSingleCase[Lbl <: String, A](using label: SingletonType[Lbl]): (IsCaseOf[Lbl, Lbl :: A] with { type Type = A })

  given isLastCase[Init, Lbl <: String, Z](using label: SingletonType[Lbl]): (IsCaseOf[Lbl, Init || (Lbl :: Z)] with { type Type = Z })

  given isInitCase[Lbl, Init, ZLbl, Z](using j: IsCaseOf[Lbl, Init]): (IsCaseOf[Lbl, Init || (ZLbl :: Z)] with { type Type = j.Type })

  given distFSingle[F[_], Lbl <: String, A](using label: SingletonType[Lbl]): (DistF[F, Lbl :: A] with { type Out = Lbl :: F[A] })

  given distFSnoc[F[_], Init, Label <: String, Z](using
    init: DistF[F, Init],
    label: SingletonType[Label],
  ): (DistF[F, Init || (Label :: Z)] with { type Out = init.Out || (Label :: F[Z]) })

  val Handlers: HandlersModule

  trait HandlersModule {
    type Builder[Cases, RemainingCases, R]

    def single[Lbl <: String, A, R](
      label: SingletonType[Lbl],
      h: A -> R,
    ): Handlers[Lbl :: A, R]

    def snoc[Init, Lbl <: String, Z, R](
      init: Handlers[Init, R],
      label: SingletonType[Lbl],
      last: Z -> R,
    ): Handlers[Init || (Lbl :: Z), R]

    def apply[Cases, R]: Builder[Cases, Cases, R]

    def apply[Cases]: InitialBuilder[Cases] =
      ()

    /** Compared to [[Builder]], defers specifying the result type. */
    opaque type InitialBuilder[Cases] =
      Unit

    extension [Cases, Init, ZLbl <: String, Z, R](b: Builder[Cases, Init || (ZLbl :: Z), R])
      def caseOf[Lbl](using SingletonType[Lbl], Lbl =:= ZLbl)(h: Z -> R): Builder[Cases, Init, R]

    extension [Cases, Lbl <: String, A, R](b: Builder[Cases, Lbl :: A, R])
      def caseOf[L](using SingletonType[L], L =:= Lbl, DummyImplicit)(h: A -> R): Handlers[Cases, R]

    extension [Init, ZLbl <: String, Z](b: InitialBuilder[Init || (ZLbl :: Z)])
      def caseOf[Lbl](using SingletonType[Lbl], Lbl =:= ZLbl): [R] => (Z -> R) => Builder[Init || (ZLbl :: Z), Init, R] =
        [R] => h => apply[Init || (ZLbl :: Z), R].caseOf[Lbl](h)

    extension [Lbl <: String, A](b: InitialBuilder[Lbl :: A])
      def caseOf[L](using SingletonType[L], L =:= Lbl, DummyImplicit): [R] => (A -> R) => Handlers[Lbl :: A, R] =
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

  def nmap[As, Bs](
    fs: ParN.Named[||, ::, ->, As, Bs],
  ): Enum[As] -> Enum[Bs] = {
    import distr.cat.*

    def go[Xs, Ys](
      fs: ParN.Named[||, ::, ->, Xs, Ys],
      nest: [Lbl] => (j: IsCaseOf[Lbl, Ys]) => IsCaseOf[Lbl, Bs] { type Type = j.Type },
    ): Handlers[Xs, Enum[Bs]] =
      fs match
        case s: ParN.Named.Single[sep, of, arr, lbl, a, b] =>
          summon[Xs =:= (lbl :: a)]
          val j = isSingleCase[lbl, b](using s.label)
          Handlers.single[lbl, a, Enum[Bs]](
            s.label,
            s.value > inject[lbl, Bs](nest(j))
          )
        case s: ParN.Named.Snoc[sep, of, arr, aInit, bInit, lbl, c, d] =>
          summon[Xs =:= (aInit || lbl :: c)]
          summon[Ys =:= (bInit || lbl :: d)]
          val j = isLastCase[bInit, lbl, d](using s.label)
          Handlers.snoc[aInit, lbl, c, Enum[Bs]](
            go[aInit, bInit](
              s.init,
              [Lbl] => (j: IsCaseOf[Lbl, bInit]) =>
                val k = isInitCase[Lbl, bInit, lbl, d](using j)
                nest(k),
            ),
            s.label,
            s.last > inject[lbl, Bs](nest(j))
          )

    handle(go[As, Bs](fs, [Lbl] => (j: IsCaseOf[Lbl, Bs]) => j))
  }
}

object EnumModule {
  def apply[->[_, _], **[_, _], Enum[_], ||[_, _], ::[_, _]](using
    cat: SemigroupalCategory[->, **],
    cocat: CocartesianNAryCategory[->, Enum, ||, ::],
    distr: DistributionNAry[->, **, Enum, ||, ::],
    i: BiInjective[||],
    j: BiInjective[::],
  ): EnumModule[->, **, Enum, ||, ::] =
    new EnumModuleImpl(cat, cocat, distr)

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
  ): EnumModule[->, **, Enum, ||, ::] = {
    val cocatN: CocartesianNAryCategory[->, Enum, ||, ::] =
      CocartesianNAryCategory.fromBinary(cocat, inj, extract, peel)
    val distN =
      DistributionNAry.fromBinary[->, **, ++, Enum, ||, ::](inj, peel, unpeel, extract)(using cat, cocat, distr)
    EnumModuleImpl[->, **, Enum, ||, ::](cat, cocatN, distN)
  }
}

private[lambda] class EnumModuleImpl[->[_, _], **[_, _], Enum[_], ||[_, _], ::[_, _]](
  cat: SemigroupalCategory[->, **],
  cocat: CocartesianNAryCategory[->, Enum, ||, ::],
  val distr: DistributionNAry[->, **, Enum, ||, ::],
)(using
  BiInjective[||],
  BiInjective[::],
) extends EnumModule[->, **, Enum, ||, ::] {
  import cat.*
  import distr.DistF

  private type Injector[Label, A, Cases] = libretto.lambda.Member[||, ::, Label, A, Cases]

  override opaque type IsCaseOf[Label, Cases] <: { type Type } = Injector[Label, ?, Cases]
  override opaque type EnumPartition[Cases, P] = Injector[?, P, Cases]
  override opaque type Handlers[Cases, R] = SinkNAryNamed[->, ||, ::, Cases, R]

  override opaque type Partitioning[Cases] <: libretto.lambda.Partitioning[->, **, Enum[Cases]] {
    type Partition[P] = EnumPartition[Cases, P]
  } =
    PartitioningImpl[Cases]

  override def inject[Lbl, Cases](c: IsCaseOf[Lbl, Cases]): c.Type -> Enum[Cases] =
    cocat.inject[Lbl, c.Type, Cases](c)

  override def handle[Cases, R](handlers: Handlers[Cases, R]): Enum[Cases] -> R =
    cocat.handle(handlers)

  override def distF[F[_], Cases](using F: Focus[**, F], ev: DistF[F, Cases]): F[Enum[Cases]] -> Enum[ev.Out] =
    ev.operationalize(F).compile

  override def distLR[A, Cases](using ev: DistLR[A, Cases]): (A ** Enum[Cases]) -> Enum[ev.Out] =
    distF[[x] =>> A ** x, Cases](using Focus.snd, ev)

  override def distRL[B, Cases](using ev: DistRL[B, Cases]): (Enum[Cases] ** B) -> Enum[ev.Out] =
    distF[[x] =>> x ** B, Cases](using Focus.fst, ev)

  override def isSingleCase[Lbl <: String, A](using label: SingletonType[Lbl]): (IsCaseOf[Lbl, Lbl :: A] with { type Type = A }) =
    Member.Single(label)

  override def isLastCase[Init, Lbl <: String, Z](using
    lbl: SingletonType[Lbl],
  ): (IsCaseOf[Lbl, Init || (Lbl :: Z)] with { type Type = Z }) =
    Member.InLast(lbl)

  override given isInitCase[Lbl, Init, ZLbl, Z](using
    j: IsCaseOf[Lbl, Init],
  ): (IsCaseOf[Lbl, Init || (ZLbl :: Z)] with { type Type = j.Type }) =
    Member.InInit(j)

  override given distFSingle[F[_], Lbl <: String, A](using label: SingletonType[Lbl]): (DistF[F, Lbl :: A] with { type Out = Lbl :: F[A] }) =
    DistF.Single(label)
  override given distFSnoc[F[_], Init, Label <: String, Z](using
    init: DistF[F, Init],
    label: SingletonType[Label],
  ): (DistF[F, Init || (Label :: Z)] with { type Out = init.Out || (Label :: F[Z]) }) =
    DistF.Snoc(init, label)

  override object Handlers extends HandlersModule {

    override opaque type Builder[Cases, RemainingCases, R] =
      HandlersBuilder[Cases, RemainingCases, R]

    override def single[Lbl <: String, A, R](label: SingletonType[Lbl], h: A -> R): Handlers[Lbl :: A, R] =
      SinkNAryNamed.single(label, h)

    override def snoc[Init, Lbl <: String, Z, R](
      init: Handlers[Init, R],
      label: SingletonType[Lbl],
      last: Z -> R,
    ): Handlers[Init || (Lbl :: Z), R] =
      SinkNAryNamed.snoc(init, label, last)

    override def apply[Cases, R]: Builder[Cases, Cases, R] =
      HandlersBuilder.Empty()

    extension [Cases, Init, ZLbl <: String, Z, R](b: Builder[Cases, Init || (ZLbl :: Z), R])
      override def caseOf[Lbl](using SingletonType[Lbl], Lbl =:= ZLbl)(h: Z -> R): Builder[Cases, Init, R] =
        HandlersBuilder.addHandler(b, summon[SingletonType[Lbl]].as[ZLbl], h)

    extension [Cases, Lbl <: String, A, R](b: Builder[Cases, Lbl :: A, R])
      override def caseOf[L](using SingletonType[L], L =:= Lbl, DummyImplicit)(h: A -> R): Handlers[Cases, R] =
        val lbl: SingletonType[Lbl] = summon[L =:= Lbl].substituteCo(summon[SingletonType[L]])
        HandlersBuilder.build(b, lbl, h)
  }

  override def partitioning[Cases](using ev: CaseList[Cases]): Partitioning[Cases] =
    PartitioningImpl(ev)

  override def toPartition[Cases, C](
    ev: IsCaseOf[C, Cases],
  ): EnumPartition[Cases, ev.Type] =
    ev

  private sealed trait HandlersBuilder[Cases, RemainingCases, R]
  private object HandlersBuilder {
    case class Empty[Cases, R]() extends HandlersBuilder[Cases, Cases, R]
    case class Snoc[Cases, Init, Lbl <: String, Z, R](
      init: HandlersBuilder[Cases, Init || (Lbl :: Z), R],
      label: SingletonType[Lbl],
      last: Z -> R,
    ) extends HandlersBuilder[Cases, Init, R]
    def addHandler[Cases, Init, Lbl <: String, B, R](
      b: HandlersBuilder[Cases, Init || (Lbl :: B), R],
      label: SingletonType[Lbl],
      h: B -> R,
    ): HandlersBuilder[Cases, Init, R] =
      Snoc(b, label, h)
    def build[Cases, Lbl <: String, Z, R](
      b: HandlersBuilder[Cases, Lbl :: Z, R],
      lbl: SingletonType[Lbl],
      h: Z -> R,
    ): Handlers[Cases, R] =
      build[Cases, Lbl :: Z, R](b, SinkNAryNamed.single(lbl, h))
    def build[Cases, Cases0, R](
      b: HandlersBuilder[Cases, Cases0, R],
      acc: Handlers[Cases0, R],
    ): Handlers[Cases, R] =
      b match
        case Empty() =>
          acc
        case Snoc(init, lbl, last) =>
          build(init, SinkNAryNamed.snoc(acc, lbl, last))
  }

  private def distHandlers[F[_], Cases, R, G[_]](
    d: DistF[F, Cases],
    h: [X] => Injector[?, X, Cases] => G[F[X] -> R],
  )(using
    G: Applicative[G],
  ): G[Handlers[d.Out, R]] = {
    type H[F[_], Cases, Out] = G[Handlers[Out, R]]
    d.fold[H](
      [LblX <: String, X] => ev ?=> s => h[X](ev.substituteCo(Member.Single(s.label))).map(SinkNAryNamed.single(s.label, _)),
      [Init, LblX <: String, X, FInit] => ev ?=> s => {
        val h2: [Y] => Injector[?, Y, Init] => G[F[Y] -> R] =
          [Y] => i => h[Y](ev.substituteCo(i.inInit))
        val hLast: G[Handlers[LblX :: F[X], R]] = h[X](ev.substituteCo(Member.InLast(s.label))).map(SinkNAryNamed.single(s.label, _))
        val hInit: G[Handlers[FInit, R]]        = distHandlers(s.init, h2)
        G.map2(hInit, hLast)(SinkNAryNamed.snoc(_, s.label, _))
      }
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
      p.label.value

    override def reinject[P](p: Injector[?, P, Cases]): P -> Enum[Cases] =
      cocat.inject(p)

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
        DistF.intoCases(cases)
      val handlers: G[Handlers[d.Out, R]] =
        distHandlers(d, handleAnyPartition)
      handlers.map { handlers =>
        distF(using pos, d) > handle(handlers)
      }
  }
}
