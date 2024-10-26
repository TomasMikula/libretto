package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, StaticValue, TypeEq, TypeEqK}
import libretto.lambda.util.TypeEqK.Refl
import libretto.lambda.util.unapply.Unapply

trait EnumModule[->[_, _], **[_, _], Enum[_], ||[_, _], ::[_, _]] {
  import EnumModule.*

  /** Witnesses that `Cases` is a list of cases, usable in `Enum`,
   * i.e. that `Cases` is of the form `(Name1 :: T1) || ... || (NameN :: TN)`.
   */
  type CaseList[Cases] = ItemList[||, ::, Cases]

  type IsCaseOf[Label, Cases] <: AnyRef with { type Type }
  type EnumPartition[Cases, P]
  type Handlers[Cases, R]
  type DistF[F[_], Cases] <: { type Out }

  type DistLR[A, Cases] = DistF[[x] =>> A ** x, Cases]
  type DistRL[B, Cases] = DistF[[x] =>> x ** B, Cases]

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

  given isSingleCase[Lbl <: String, A](using label: StaticValue[Lbl]): (IsCaseOf[Lbl, Lbl :: A] with { type Type = A })
  given isLastCase[Init, Lbl <: String, Z](using StaticValue[Lbl]): (IsCaseOf[Lbl, Init || (Lbl :: Z)] with { type Type = Z })
  given isInitCase[Lbl, Init, ZLbl, Z](using j: IsCaseOf[Lbl, Init]): (IsCaseOf[Lbl, Init || (ZLbl :: Z)] with { type Type = j.Type })

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

  given SemigroupalCategory[->, **] = cat

  val cocatN: CocartesianNAryCategory[->, Enum, ||, ::] =
    CocartesianNAryCategory.fromBinary(cocat, inj, extract, peel)

  val distN =
    DistributionNAry.fromBinary[->, **, ++, Enum, ||, ::](inj, peel, unpeel, extract)(using cat, cocat, distr)

  export distN.DistF

  private type Injector[Label, A, Cases] = libretto.lambda.Member[||, ::, Label, A, Cases]

  override opaque type IsCaseOf[Label, Cases] <: { type Type } = Injector[Label, ?, Cases]
  override opaque type EnumPartition[Cases, P] = Injector[?, P, Cases]
  override opaque type Handlers[Cases, R] = SinkNAry[->, ||, ::, Cases, R]

  override opaque type Partitioning[Cases] <: libretto.lambda.Partitioning[->, **, Enum[Cases]] {
    type Partition[P] = EnumPartition[Cases, P]
  } =
    PartitioningImpl[Cases]

  override def inject[Cases](label: String)(using c: IsCaseOf[label.type, Cases]): c.Type -> Enum[Cases] =
    cocatN.inject[label.type, c.Type, Cases](c)

  override def handle[Cases, R](handlers: Handlers[Cases, R]): Enum[Cases] -> R =
    cocatN.handle(handlers)

  override def distF[F[_], Cases](using F: Focus[**, F], ev: DistF[F, Cases]): F[Enum[Cases]] -> Enum[ev.Out] =
    ev.operationalize(F).compile

  override def distLR[A, Cases](using ev: DistLR[A, Cases]): (A ** Enum[Cases]) -> Enum[ev.Out] =
    distF[[x] =>> A ** x, Cases](using Focus.snd, ev)

  override def distRL[B, Cases](using ev: DistRL[B, Cases]): (Enum[Cases] ** B) -> Enum[ev.Out] =
    distF[[x] =>> x ** B, Cases](using Focus.fst, ev)

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

  override given distFSingle[F[_], Lbl <: String, A](using label: StaticValue[Lbl]): (DistF[F, Lbl :: A] with { type Out = Lbl :: F[A] }) =
    DistF.Single(label.value)
  override given distFSnoc[F[_], Init, Label <: String, Z](using
    init: DistF[F, Init],
    label: StaticValue[Label],
  ): (DistF[F, Init || (Label :: Z)] with { type Out = init.Out || (Label :: F[Z]) }) =
    DistF.Snoc(init, label.value)

  override object Handlers extends HandlersModule {

    override opaque type Builder[Cases, RemainingCases, R] =
      HandlersBuilder[Cases, RemainingCases, R]

    override def single[Lbl, A, R](h: A -> R): Handlers[Lbl :: A, R] =
      SinkNAry.Single(h)

    override def snoc[Init, Lbl, Z, R](
      init: Handlers[Init, R],
      last: Z -> R,
    ): Handlers[Init || (Lbl :: Z), R] =
      SinkNAry.Snoc(init, last)

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
    ): Handlers[Cases, R] =
      build[Cases, Lbl :: Z, R](b, SinkNAry.Single(h))
    def build[Cases, Cases0, R](
      b: HandlersBuilder[Cases, Cases0, R],
      acc: Handlers[Cases0, R],
    ): Handlers[Cases, R] =
      b match
        case Empty()          => acc
        case Snoc(init, last) => build(init, SinkNAry.Snoc(acc, last))
  }

  private def distHandlers[F[_], Cases, R, G[_]](
    d: DistF[F, Cases],
    h: [X] => Injector[?, X, Cases] => G[F[X] -> R],
  )(using
    G: Applicative[G],
  ): G[Handlers[d.Out, R]] = {
    type H[F[_], Cases, Out] = G[Handlers[Out, R]]
    d.fold[H](
      [LblX <: String, X] => ev ?=> s => h[X](ev.substituteCo(Member.Single(s.label))).map(SinkNAry.Single(_)),
      [Init, LblX <: String, X, FInit] => ev ?=> s => {
        val h2: [Y] => Injector[?, Y, Init] => G[F[Y] -> R] =
          [Y] => i => h[Y](ev.substituteCo(i.inInit))
        val hLast: G[Handlers[LblX :: F[X], R]] = h[X](ev.substituteCo(Member.InLast(s.lbl))).map(SinkNAry.Single(_))
        val hInit: G[Handlers[FInit, R]]        = distHandlers(s.init, h2)
        G.map2(hInit, hLast)(SinkNAry.snoc(_, _))
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
      p.label

    override def reinject[P](p: Injector[?, P, Cases]): P -> Enum[Cases] =
      cocatN.inject(p)

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
