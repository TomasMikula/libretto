package libretto.lambda.examples.workflow.generic.lang

import libretto.lambda.{CocartesianNAryCategory, CocartesianSemigroupalCategory, Distribution, DistributionNAry, EnumModule, Member, Shuffled, ShuffledModule, SinkNAryNamed, SymmetricSemigroupalCategory}
import libretto.lambda.util.Masked

import scala.concurrent.duration.FiniteDuration

sealed trait FlowAST[Op[_, _], A, B] {
  import FlowAST.*

  def >>>[C](that: FlowAST[Op, B, C]): FlowAST[Op, A, C] =
    FlowAST.andThen(this, that)

  def maskInput: Masked[[a] =>> FlowAST[Op, a, B], A] =
    Masked(this)

  def from[Z](using ev: Z =:= A): FlowAST[Op, Z, B] =
    ev.substituteContra[FlowAST[Op, _, B]](this)

  def to[C](using ev: B =:= C): FlowAST[Op, A, C] =
    ev.substituteCo(this)

  def translate[F[_, _]](h: [x, y] => Op[x, y] => F[x, y]): FlowAST[F, A, B] =
    this match {
      case Ext(action)                  => Ext(h(action))
      case AndThen(f, g)                => AndThen(f.translate(h), g.translate(h))
      case Par(f1, f2)                  => Par(f1.translate(h), f2.translate(h))
      case Handle(handlers)             => Handle(handlers.translate([x, y] => _.translate(h)))
      case DoWhile(f)                   => DoWhile(f.translate(h))
      case Id()                         => Id()
      case _: Swap[op, x, y]            => Swap[F, x, y]()
      case _: AssocLR[op, x, y, z]      => AssocLR[F, x, y, z]()
      case _: AssocRL[op, x, y, z]      => AssocRL[F, x, y, z]()
      case i: Inject[op, l, a, cases]   => Inject[F, l, a, cases](i.i)
      case _: Prj1[op, x, y]            => Prj1[F, x, y]()
      case _: Prj2[op, x, y]            => Prj2[F, x, y]()
      case Dup()                        => Dup()
      case IntroFst()                   => IntroFst()
      case IntroSnd()                   => IntroSnd()
      case DistributeNAryLR(d)          => DistributeNAryLR(d)
      case DistributeNAryRL(d)          => DistributeNAryRL(d)
      case _: Read[op, x]               => Read[F, x]()
      case _: ReadAwait[op, x]          => ReadAwait[F, x]()
      case r: ReadAwaitTimeout[op, x]   => ReadAwaitTimeout[F, x](r.duration)
      case Delay(duration)              => Delay(duration)
    }

  def toShuffled(using shuffled: ShuffledModule[FlowAST.Work[Op, _, _], **]): shuffled.Shuffled[A, B] =
    this match
      case Id()                    => shuffled.id
      case AndThen(f, g)           => f.toShuffled > g.toShuffled
      case _: AssocLR[op, x, y, z] => shuffled.assocLR[x, y, z]
      case _: AssocRL[op, x, y, z] => shuffled.assocRL[x, y, z]
      case Par(f1, f2)             => shuffled.par(f1.toShuffled, f2.toShuffled)
      case _: Swap[op, x, y]       => shuffled.swap[x, y]
      case f: Work[Op, A, B]       => shuffled.lift(f)

}

object FlowAST {
  case class Id[Op[_, _], A]() extends FlowAST[Op, A, A]
  case class AndThen[Op[_, _], A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]) extends FlowAST[Op, A, C]
  case class AssocLR[Op[_, _], A, B, C]() extends FlowAST[Op, (A ** B) ** C, A ** (B ** C)]
  case class AssocRL[Op[_, _], A, B, C]() extends FlowAST[Op, A ** (B ** C), (A ** B) ** C]
  case class Par[Op[_, _], A1, A2, B1, B2](f1: FlowAST[Op, A1, B1], f2: FlowAST[Op, A2, B2]) extends FlowAST[Op, A1 ** A2, B1 ** B2]
  case class Swap[Op[_, _], A, B]() extends FlowAST[Op, A ** B, B ** A]

  sealed trait Work[Op[_, _], A, B] extends FlowAST[Op, A, B] {
    override def maskInput: Masked[[a] =>> Work[Op, a, B], A] =
      Masked(this)
  }
  case class IntroFst[Op[_, _], A]() extends Work[Op, A, Unit ** A]
  case class IntroSnd[Op[_, _], A]() extends Work[Op, A, A ** Unit]
  case class Prj1[Op[_, _], A, B]() extends Work[Op, A ** B, A]
  case class Prj2[Op[_, _], A, B]() extends Work[Op, A ** B, B]
  case class Dup[Op[_, _], A]() extends Work[Op, A, A ** A]
  case class Inject[Op[_, _], Label, A, Cases](i: Member[||, ::, Label, A, Cases]) extends Work[Op, A, Enum[Cases]]
  case class Handle[Op[_, _], Cases, B](handlers: SinkNAryNamed[FlowAST[Op, _, _], ||, ::, Cases, B]) extends Work[Op, Enum[Cases], B]
  case class DistributeNAryLR[Op[_, _], A, Cases, ACases](
    dist: DistributionNAry.DistLR[**, ||, ::, A, Cases] { type Out = ACases },
  ) extends Work[Op, A ** Enum[Cases], Enum[ACases]]
  case class DistributeNAryRL[Op[_, _], B, Cases, BCases](
    dist: DistributionNAry.DistRL[**, ||, ::, B, Cases] { type Out = BCases },
  ) extends Work[Op, Enum[Cases] ** B, Enum[BCases]]
  case class DoWhile[Op[_, _], A, B](f: FlowAST[Op, A, A ++ B]) extends Work[Op, A, B]
  case class Delay[Op[_, _], A](duration: FiniteDuration) extends Work[Op, A, A]

  case class Read[Op[_, _], A]() extends Work[Op, Unit, PortName[A] ** Reading[A]]
  case class ReadAwait[Op[_, _], A]() extends Work[Op, Reading[A], A]
  case class ReadAwaitTimeout[Op[_, _], A](duration: FiniteDuration) extends Work[Op, Reading[A], A ++ Reading[A]]

  /** Extension point for pluggable actions. */
  case class Ext[Op[_, _], A, B](action: Op[A, B]) extends Work[Op, A, B]

  given ssc[Op[_, _]]: SymmetricSemigroupalCategory[FlowAST[Op, _, _], **] with {
    override def id[A]: FlowAST[Op, A, A] = Id()
    override def andThen[A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]): FlowAST[Op, A, C] = FlowAST.andThen(f, g)
    override def assocLR[A, B, C]: FlowAST[Op, (A ** B) ** C, A ** (B ** C)] = AssocLR()
    override def assocRL[A, B, C]: FlowAST[Op, A ** (B ** C), (A ** B) ** C] = AssocRL()
    override def par[A1, A2, B1, B2](f1: FlowAST[Op, A1, B1], f2: FlowAST[Op, A2, B2]): FlowAST[Op, A1 ** A2, B1 ** B2] = FlowAST.par(f1, f2)
    override def swap[A, B]: FlowAST[Op, A ** B, B ** A] = Swap()
  }

  def injectL[Op[_, _], A, B]: FlowAST[Op, A, A ++ B] = Inject(summon)
  def injectR[Op[_, _], A, B]: FlowAST[Op, B, A ++ B] = Inject(summon)
  def either[Op[_, _], A, B, C](f: FlowAST[Op, A, C], g: FlowAST[Op, B, C]): FlowAST[Op, A ++ B, C] =
      Handle(SinkNAryNamed.Single(f) || g)

  given cocat[Op[_, _]]: CocartesianSemigroupalCategory[FlowAST[Op, _, _], ++] with {
    override def andThen[A, B, C](f: FlowAST[Op, A, B], g: FlowAST[Op, B, C]): FlowAST[Op, A, C] = FlowAST.andThen(f, g)
    override def id[A]: FlowAST[Op, A, A] = Id()
    override def injectL[A, B]: FlowAST[Op, A, A ++ B] = FlowAST.injectL[Op, A, B]
    override def injectR[A, B]: FlowAST[Op, B, A ++ B] = FlowAST.injectR[Op, A, B]
    override def either[A, B, C](f: FlowAST[Op, A, C], g: FlowAST[Op, B, C]): FlowAST[Op, A ++ B, C] =
      FlowAST.either(f, g)
  }

  given cocatN[Op[_, _]]: CocartesianNAryCategory[FlowAST[Op, _, _], Enum, ||, ::] with {
    override def inject[Label, A, Cases](
      i: Member[||, ::, Label, A, Cases],
    ): FlowAST[Op, A, Enum[Cases]] =
      Inject(i)

    override def handle[Cases, R](
      handlers: SinkNAryNamed[FlowAST[Op, _, _], ||, ::, Cases, R],
    ): FlowAST[Op, Enum[Cases], R] =
      Handle(handlers)
  }

  def distributeLR[Op[_, _], A, B, C]: FlowAST[Op, A ** (B ++ C), A ** B ++ A ** C] =
    DistributeNAryLR(DistributionNAry.DistLR.Single("Left").extend("Right"))

  def distributeRL[Op[_, _], A, B, C]: FlowAST[Op, (A ++ B) ** C, A ** C ++ B ** C] =
    DistributeNAryRL(DistributionNAry.DistRL.Single("Left").extend("Right"))

  given distr[Op[_, _]]: Distribution[FlowAST[Op, _, _], **, ++] with {
    override val cat: SymmetricSemigroupalCategory[FlowAST[Op, _, _], **] = ssc[Op]
    import cat.*
    override def distLR[A, B, C]: FlowAST[Op, A ** (B ++ C), A ** B ++ A ** C] =
      FlowAST.distributeLR[Op, A, B, C]

    override def distRL[A, B, C]: FlowAST[Op, (A ++ B) ** C, A ** C ++ B ** C] =
      FlowAST.distributeRL[Op, A, B, C]
  }

  given distrN[Op[_, _]]: DistributionNAry[FlowAST[Op, _, _], **, Enum, ||, ::] with {
    override val cat =
      ssc[Op]

    override def distLR[A, Cases](
      witness: DistLR[A, Cases],
    ): FlowAST[Op, A ** Enum[Cases], Enum[witness.Out]] =
      DistributeNAryLR(witness)

    override def distRL[B, Cases](
      witness: DistRL[B, Cases],
    ): FlowAST[Op, Enum[Cases] ** B, Enum[witness.Out]] =
      DistributeNAryRL(witness)
  }

  given enumModule[Op[_, _]]: EnumModule[FlowAST[Op, _, _], **, Enum, ||, ::] =
    EnumModule[FlowAST[Op, _, _], **, Enum, ||, ::]

  def shuffled[Op[_, _]]: ShuffledModule[Work[Op, _, _], **] =
    Shuffled[Work[Op, _, _], **]

  def fromShuffled[Op[_, _], A, B](using
    shuffled: ShuffledModule[FlowAST.Work[Op, _, _], **],
  )(
    f: shuffled.Shuffled[A, B],
  ): FlowAST[Op, A, B] =
    f.foldMap[FlowAST[Op, _, _]]([x, y] => (w: Work[Op, x, y]) => w)

  def andThen[Op[_, _], A, B, C](
    f: FlowAST[Op, A, B],
    g: FlowAST[Op, B, C],
  ): FlowAST[Op, A, C] =
    (f, g) match
      case (Id(), g) => g
      case (f, Id()) => f
      case (f, g) => AndThen(f, g)

  def par[Op[_, _], A1, A2, B1, B2](
    f1: FlowAST[Op, A1, B1],
    f2: FlowAST[Op, A2, B2],
  ): FlowAST[Op, A1 ** A2, B1 ** B2] =
    (f1, f2) match
      case (Id(), Id()) => Id()
      case (f1, f2) => Par(f1, f2)

  // TODO: have a normalized representation. Then this method will become superfluous.
  /** _Might_ simplify the FlowAST. */
  def shakeUp[Op[_, _], A, B](
    f: FlowAST[Op, A, B],
  ): FlowAST[Op, A, B] =
    given ShuffledModule[Work[Op, _, _], **] = shuffled[Op]
    fromShuffled(f.toShuffled)
}
