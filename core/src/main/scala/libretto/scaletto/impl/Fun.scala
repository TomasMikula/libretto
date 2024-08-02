package libretto.scaletto.impl

import libretto.lambda.{ClosedSymmetricMonoidalCategory, CocartesianSemigroupalCategory, Distribution, Member, SemigroupalCategory}
import libretto.lambda.util.{Applicative, SourcePos, TypeEq, Validated}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.util.Validated.{Valid, invalid}
import scala.annotation.tailrec
import scala.concurrent.duration.FiniteDuration

import phantoms.*

sealed trait Fun[+ ->[_, _], A, B] {
  import Fun.*

  def translateA[->>[_, _], G[_]](
    h: [X, Y] => (X -> Y) => G[X ->> Y],
  )(using
    G: Applicative[G],
  ): G[Fun[->>, A, B]] =
    this match
      case l: Leaf[A, B] => G.pure(l: Fun[->>, A, B])
      case AndThen(f, g) => G.map2(h(f), h(g)) { AndThen(_, _) }
      case Par(f1, f2) => G.map2(h(f1), h(f2)) { Par(_, _) }
      case EitherF(f, g) => G.map2(h(f), h(g)) { EitherF(_, _) }
      case Choice(f, g) => G.map2(h(f), h(g)) { Choice(_, _) }
      case c: CaptureIntoSub[arr, x, a, b] => G.map2(h(c.discardCapture), h(c.splitCapture)) { CaptureIntoSub[->>, x, a, b](_, _) }
      case RecFun(f) => h(f).map { RecFun(_) }

  def foldMonoid[M](
    h: [X, Y] => (X -> Y) => M,
  )(using
    M: Monoid[M],
  ): M = {
    this match
      case _: Leaf[A, B] => M.unit
      case AndThen(f, g) => h(f) <> h(g)
      case Par(f1, f2) => h(f1) <> h(f2)
      case EitherF(f, g) => h(f) <> h(g)
      case Choice(f, g) => h(f) <> h(g)
      case CaptureIntoSub(dis, spl) => h(dis) <> h(spl)
      case RecFun(f) => h(f)
  }
}

object Fun {
  sealed trait Leaf[A, B] extends Fun[Nothing, A, B]

  case class AndThen[->[_, _], A, B, C](
    f: A -> B,
    g: B -> C,
  ) extends Fun[->, A, C]

  case class Par[->[_, _], A1, A2, B1, B2](
    f1: A1 -> B1,
    f2: A2 -> B2,
  ) extends Fun[->, A1 |*| A2, B1 |*| B2]

  case class EitherF[->[_, _], A, B, C](
    f: A -> C,
    g: B -> C,
  ) extends Fun[->, A |+| B, C]

  case class Choice[->[_, _], A, B, C](
    f: A -> B,
    g: A -> C,
  ) extends Fun[->, A, B |&| C]

  case class RecFun[->[_, _], A, B](
    f: (Sub[A, B] |*| A) -> B,
  ) extends Fun[->, A, B]

  case class CaptureIntoSub[->[_, _], X, A, B](
    discardCapture: X -> One,
    splitCapture: X -> (X |*| X),
  ) extends Fun[->, Sub[X |*| A, B] |*| X, Sub[A, B]]

  case class Id[A]() extends Leaf[A, A]
  case class IntroFst[B]() extends Leaf[B, One |*| B]
  case class IntroSnd[A]() extends Leaf[A, A |*| One]
  case class ElimFst[B]() extends Leaf[One |*| B, B]
  case class ElimSnd[A]() extends Leaf[A |*| One, A]
  case class AssocLR[A, B, C]() extends Leaf[(A |*| B) |*| C, A |*| (B |*| C)]
  case class AssocRL[A, B, C]() extends Leaf[A |*| (B |*| C), (A |*| B) |*| C]
  case class Swap[A, B]() extends Leaf[A |*| B, B |*| A]
  case class InjectL[A, B]() extends Leaf[A, A |+| B]
  case class InjectR[A, B]() extends Leaf[B, A |+| B]
  case class Absurd[A]() extends Leaf[Void, A]
  case class OneOfInject[Label, A, Cases](i: Member[[x, y] =>> y || x, ::, Label, A, Cases]) extends Leaf[A, OneOf[Cases]]
  case class OneOfPeel[Label, A, Cases]() extends Leaf[OneOf[Cases || (Label :: A)], A |+| OneOf[Cases]]
  case class OneOfUnpeel[Label, A, Cases]() extends Leaf[A |+| OneOf[Cases], OneOf[Cases || (Label :: A)]]
  case class OneOfExtractSingle[Lbl, A]() extends Leaf[OneOf[Lbl :: A], A]
  case class ChooseL[A, B]() extends Leaf[A |&| B, A]
  case class ChooseR[A, B]() extends Leaf[A |&| B, B]
  case class PingF() extends Leaf[One, Ping]
  case class PongF() extends Leaf[Pong, One]
  case class DelayIndefinitely() extends Leaf[Done, RTerminus]
  case class RegressInfinitely() extends Leaf[LTerminus, Need]
  case class Fork() extends Leaf[Done, Done |*| Done]
  case class Join() extends Leaf[Done |*| Done, Done]
  case class ForkNeed() extends Leaf[Need |*| Need, Need]
  case class JoinNeed() extends Leaf[Need, Need |*| Need]
  case class NotifyDoneL() extends Leaf[Done, Ping |*| Done]
  case class NotifyNeedL() extends Leaf[Pong |*| Need, Need]
  case class ForkPing() extends Leaf[Ping, Ping |*| Ping]
  case class ForkPong() extends Leaf[Pong |*| Pong, Pong]
  case class JoinPing() extends Leaf[Ping |*| Ping, Ping]
  case class JoinPong() extends Leaf[Pong, Pong |*| Pong]
  case class StrengthenPing() extends Leaf[Ping, Done]
  case class StrengthenPong() extends Leaf[Need, Pong]
  case class JoinRTermini() extends Leaf[RTerminus |*| RTerminus, RTerminus]
  case class JoinLTermini() extends Leaf[LTerminus, LTerminus |*| LTerminus]
  case class NotifyEither[A, B]() extends Leaf[A |+| B, Ping |*| (A |+| B)]
  case class NotifyChoice[A, B]() extends Leaf[Pong |*| (A |&| B), A |&| B]
  case class InjectLOnPing[A, B]() extends Leaf[Ping |*| A, A |+| B]
  case class ChooseLOnPong[A, B]() extends Leaf[A |&| B, Pong |*| A]
  case class DistributeL[A, B, C]() extends Leaf[A |*| (B |+| C), (A |*| B) |+| (A |*| C)]
  case class CoDistributeL[A, B, C]() extends Leaf[(A |*| B) |&| (A |*| C), A |*| (B |&| C)]
  case class RInvertSignal() extends Leaf[Done |*| Need, One]
  case class LInvertSignal() extends Leaf[One, Need |*| Done]
  case class RInvertPingPong() extends Leaf[Ping |*| Pong, One]
  case class LInvertPongPing() extends Leaf[One, Pong |*| Ping]
  case class RInvertTerminus() extends Leaf[RTerminus |*| LTerminus, One]
  case class LInvertTerminus() extends Leaf[One, LTerminus |*| RTerminus]
  case class InvokeSub[A, B]() extends Leaf[Sub[A, B] |*| A, B]
  case class IgnoreSub[A, B]() extends Leaf[Sub[A, B], One]
  case class DupSub[A, B]() extends Leaf[Sub[A, B], Sub[A, B] |*| Sub[A, B]]
  case class Pack[F[_]]() extends Leaf[F[Rec[F]], Rec[F]]
  case class Unpack[F[_]]() extends Leaf[Rec[F], F[Rec[F]]]
  case class RacePair() extends Leaf[Ping |*| Ping, One |+| One]
  case class SelectPair() extends Leaf[One |&| One, Pong |*| Pong]

  case class Forevert[A]() extends Leaf[One, -[A] |*| A]
  case class Backvert[A]() extends Leaf[A |*| -[A], One]
  case class DistributeInversion[A, B]() extends Leaf[-[A |*| B], -[A] |*| -[B]]
  case class FactorOutInversion[A, B]() extends Leaf[-[A] |*| -[B], -[A |*| B]]

  case class CrashWhenDone[A, B](msg: String) extends Leaf[Done |*| A, B]
  case class Delay() extends Leaf[Val[FiniteDuration], Done]
  case class LiftEither[A, B]() extends Leaf[Val[Either[A, B]], Val[A] |+| Val[B]]
  case class LiftPair[A, B]() extends Leaf[Val[(A, B)], Val[A] |*| Val[B]]
  case class UnliftPair[A, B]() extends Leaf[Val[A] |*| Val[B], Val[(A, B)]]
  case class MapVal[A, B](f: ScalaFunction[A, B]) extends Leaf[Val[A], Val[B]]
  case class ConstVal[A](a: A) extends Leaf[Done, Val[A]]
  case class ConstNeg[A](a: A) extends Leaf[-[Val[A]], Need]
  case class Neglect[A]() extends Leaf[Val[A], Done]
  case class NotifyVal[A]() extends Leaf[Val[A], Ping |*| Val[A]]
  case class NotifyNeg[A]() extends Leaf[Pong |*| -[Val[A]], -[Val[A]]]
  case class DebugPrint(msg: String) extends Leaf[Ping, One]

  case class Acquire[A, R, B](
    acquire: ScalaFunction[A, (R, B)],
    release: Option[ScalaFunction[R, Unit]],
  ) extends Leaf[Val[A], Res[R] |*| Val[B]]

  case class TryAcquire[A, R, B, E](
    acquire: ScalaFunction[A, Either[E, (R, B)]],
    release: Option[ScalaFunction[R, Unit]],
  ) extends Leaf[Val[A], Val[E] |+| (Res[R] |*| Val[B])]

  case class Release[R]() extends Leaf[Res[R], Done]
  case class ReleaseWith[R, A, B](f: ScalaFunction[(R, A), B]) extends Leaf[Res[R] |*| Val[A], Val[B]]
  case class Effect[R, A, B](f: ScalaFunction[(R, A), B]) extends Leaf[Res[R] |*| Val[A], Res[R] |*| Val[B]]
  case class EffectWr[R, A](f: ScalaFunction[(R, A), Unit]) extends Leaf[Res[R] |*| Val[A], Res[R]]

  case class TryEffectAcquire[R, A, S, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, B)]],
    release: Option[ScalaFunction[S, Unit]],
  ) extends Leaf[Res[R] |*| Val[A], Res[R] |*| (Val[E] |+| (Res[S] |*| Val[B]))]

  case class TryTransformResource[R, A, S, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, B)]],
    release: Option[ScalaFunction[S, Unit]],
  ) extends Leaf[Res[R] |*| Val[A], Val[E] |+| (Res[S] |*| Val[B])]

  case class TrySplitResource[R, A, S, T, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, T, B)]],
    release1: Option[ScalaFunction[S, Unit]],
    release2: Option[ScalaFunction[T, Unit]],
  ) extends Leaf[Res[R] |*| Val[A], Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[B])]
}

/** Libretto function representation, allowing for auxiliary constructs like self-references.
 *
 * @see [[Blueprint]] which does not allow self-references
 */
sealed trait -⚬[A, B] {
  import -⚬.*
  import Fun.*

  def >[C](that: B -⚬ C): A -⚬ C =
    andThen(this, that)

  private[-⚬] lazy val sizeAndRefs: SizeAndRefs =
    import SizeAndRefs.one

    this match
      case r: SelfRef[A, B] =>
        one
      case FunRef(id, f) =>
        SizeAndRefs(1, Map(id -> f))
      case ConstSub(f) =>
        one + f.sizeAndRefs
      case Regular(f) =>
        one + f.foldMonoid([X, Y] => (g: X -⚬ Y) => g.sizeAndRefs)

  lazy val size: Long =
    val SizeAndRefs(n, refs) = this.sizeAndRefs
    computeSize(n, Set.empty, refs.toList)

  def blueprint: Validated[SelfRef[?, ?], Blueprint[A, B]] =
    this match
      case r: SelfRef[A, B] =>
        invalid(r)
      case FunRef(id, f) =>
        Valid(Blueprint.FunRef(id, f))
      case ConstSub(f) =>
        Valid(Blueprint.ConstSub(f))
      case Regular(f) =>
        f
          .translateA([X, Y] => _.blueprint)
          .map(Blueprint.Regular(_))
}

object -⚬ {
  import Fun.*

  case class Regular[A, B](value: Fun[-⚬, A, B]) extends (A -⚬ B)

  case class FunRef[A, B](
    id: Object, // XXX: use a proper Id type
    f: Blueprint[A, B],
  ) extends (A -⚬ B)

  case class ConstSub[A, B](
    f: Blueprint[A, B],
  ) extends (One -⚬ Sub[A, B])

  class SelfRef[A, B](
    val defnPos: SourcePos,
  ) extends (A -⚬ B) {

    infix def testEqual[X, Y](that: SelfRef[X, Y]): Option[(A =:= X, B =:= Y)] =
      Option.when(this eq that)((
        summon[A =:= A].asInstanceOf[A =:= X],
        summon[B =:= B].asInstanceOf[B =:= Y],
      ))
  }

  def id[A]: A -⚬ A =
    Regular(Id())

  def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C =
    (f, g) match
      case (Regular(Id()), g) => g
      case (f, Regular(Id())) => f
      case _                  => Regular(AndThen(f, g))

  def par[A, B, C, D](
    f: A -⚬ B,
    g: C -⚬ D,
  ): (A |*| C) -⚬ (B |*| D) =
    (f, g) match
      case (Regular(Id()), Regular(Id())) => Regular(Id())
      case _                              => Regular(Par(f, g))

  def choice[A, B, C](
    f: A -⚬ B,
    g: A -⚬ C,
  ): A -⚬ (B |&| C) =
    Regular(Choice(f, g))

  type =⚬[A, B] = -[A] |*| B

  given 𝒞: ClosedSymmetricMonoidalCategory[-⚬, |*|, One, =⚬] with {
    override def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C                              = -⚬.andThen(f, g)
    override def id[A]: A -⚬ A                                                               = -⚬.id[A]
    override def par[A1, A2, B1, B2](f1: A1 -⚬ B1, f2: A2 -⚬ B2): (A1 |*| A2) -⚬ (B1 |*| B2) = -⚬.par(f1, f2)
    override def assocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C))                    = Regular(AssocLR[A, B, C]())
    override def assocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C)                    = Regular(AssocRL[A, B, C]())
    override def swap[A, B]: (A |*| B) -⚬ (B |*| A)                                          = Regular(Swap[A, B]())
    override def elimFst[A]: (One |*| A) -⚬ A                                                = Regular(ElimFst[A]())
    override def elimSnd[A]: (A |*| One) -⚬ A                                                = Regular(ElimSnd[A]())
    override def introFst[A]: A -⚬ (One |*| A)                                               = Regular(IntroFst[A]())
    override def introSnd[A]: A -⚬ (A |*| One)                                               = Regular(IntroSnd[A]())

    override def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C) =
      introFst(Regular(Forevert[B]())) > assocLR > snd(swap > f)

    override def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B =
      swap > assocRL > elimFst(Regular(Backvert()))
  }

  val cocat: CocartesianSemigroupalCategory[-⚬, |+|] =
    new CocartesianSemigroupalCategory[-⚬, |+|] {
      override def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C = -⚬.andThen(f, g)
      override def id[A]: A -⚬ A                                  = -⚬.id[A]

      override def injectL[A, B]: A -⚬ (A |+| B)                         = Regular(InjectL())
      override def injectR[A, B]: B -⚬ (A |+| B)                         = Regular(InjectR())
      override def either[A, B, C](f: A -⚬ C, g: B -⚬ C): (A |+| B) -⚬ C = Regular(EitherF(f, g))
    }

  val distribution: Distribution[-⚬, |*|, |+|] =
    new Distribution[-⚬, |*|, |+|] {
      import cocat.{either, injectL, injectR}

      override val cat: SemigroupalCategory[-⚬, |*|] =
        𝒞

      override def distLR[A, B, C]: (A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C)) =
        Regular(DistributeL())

      override def distRL[A, B, C]: ((A |+| B) |*| C) -⚬ ((A |*| C) |+| (B |*| C)) =
        (𝒞.swap > distLR) > either(𝒞.swap > injectL, 𝒞.swap > injectR)
    }

  import cocat.*
  import distribution.*

  def ignoreSub[A, B]: Sub[A, B] -⚬ One =
    Regular(IgnoreSub())

  def dupSub[A, B]: Sub[A, B] -⚬ (Sub[A, B] |*| Sub[A, B]) =
    Regular(DupSub())

  def captureIntoSub[X, A, B](
    discardCapture: X -⚬ One,
    splitCapture: X -⚬ (X |*| X),
  ): (Sub[X |*| A, B] |*| X) -⚬ Sub[A, B] =
    Regular(CaptureIntoSub(discardCapture, splitCapture))

  def fromBlueprint[A, B](f: Blueprint[A, B]): A -⚬ B =
    f match
      case Blueprint.FunRef(id, f) =>
        FunRef(id, f)
      case Blueprint.ConstSub(f) =>
        ConstSub(f)
      case Blueprint.Regular(f) =>
        Regular(
          f match
            case l: Leaf[A, B] => l: Fun[-⚬, A, B]
            case AndThen(f, g) => AndThen(fromBlueprint(f), fromBlueprint(g))
            case Par(f, g) => Par(fromBlueprint(f), fromBlueprint(g))
            case EitherF(f, g) => EitherF(fromBlueprint(f), fromBlueprint(g))
            case Choice(f, g) => Choice(fromBlueprint(f), fromBlueprint(g))
            case RecFun(f) => RecFun(fromBlueprint(f))
            case c: CaptureIntoSub[arr, x, a, b] =>
              CaptureIntoSub[-⚬, x, a, b](
                fromBlueprint(c.discardCapture),
                fromBlueprint(c.splitCapture)
              )
        )

  def rec[A, B](
    pos: SourcePos,
    f: (A -⚬ B) => (A -⚬ B),
  ): A -⚬ B =
    val placeholder = SelfRef[A, B](pos)
    val body = f(placeholder)
    elimSelfRef(placeholder, body) match
      case None => body
      case Some(h) => Regular(RecFun(h))

  private def elimSelfRef[X, Y, A, B](
    ref: SelfRef[X, Y],
    f: A -⚬ B,
  ): Option[(Sub[X, Y] |*| A) -⚬ B] = {
    type SXY = Sub[X, Y]

    f match
      case ref1: SelfRef[a, b] =>
        (ref1 testEqual ref) map:
          case (TypeEq(Refl()), TypeEq(Refl())) =>
            summon[X =:= A]
            summon[Y =:= B]
            Regular(InvokeSub[X, Y]()): (Sub[X, Y] |*| A) -⚬ B

      case FunRef(_, _) | ConstSub(_) =>
        // FunRef and ConstSub are acyclic by construction
        None

      case Regular(f) =>
        f match
          case AndThen(g, h) =>
            (elimSelfRef(ref, g), elimSelfRef(ref, h)) match
              case (None   , None   ) => None
              case (Some(g), None   ) => Some(g > h)
              case (None   , Some(h)) => Some(𝒞.snd(g) > h)
              case (Some(g), Some(h)) => Some((𝒞.fst(dupSub) > 𝒞.assocLR) > (𝒞.snd(g) > h))
          case p: Par[arr, a1, a2, b1, b2] =>
            (elimSelfRef(ref, p.f1), elimSelfRef(ref, p.f2)) match
              case (None    , None    ) => None
              case (Some(f1), None    ) => Some(𝒞.assocRL[SXY, a1, a2] > par(f1, p.f2))
              case (None    , Some(f2)) => Some(𝒞.xi[SXY, a1, a2] > par(p.f1, f2))
              case (Some(f1), Some(f2)) => Some(𝒞.fst(dupSub) > 𝒞.ixi[SXY, SXY, a1, a2] > par(f1, f2))
          case f: EitherF[arr, a1, a2, b] =>
            (elimSelfRef(ref, f.f), elimSelfRef(ref, f.g)) match
              case (None   , None   ) => None
              case (Some(g), None   ) => Some(distLR[SXY, a1, a2] > either(g, 𝒞.elimFst(ignoreSub) > f.g))
              case (None   , Some(h)) => Some(distLR[SXY, a1, a2] > either(𝒞.elimFst(ignoreSub) > f.f, h))
              case (Some(g), Some(h)) => Some(distLR[SXY, a1, a2] > either(g, h))
          case f: Choice[arr, a, b1, b2] =>
            (elimSelfRef(ref, f.f), elimSelfRef(ref, f.g)) match
              case (None   , None   ) => None
              case (Some(g), None   ) => Some(choice(g, 𝒞.elimFst(ignoreSub) > f.g))
              case (None   , Some(h)) => Some(choice(𝒞.elimFst(ignoreSub) > f.f, h))
              case (Some(g), Some(h)) => Some(choice(g, h))
          case RecFun(g) =>
            elimSelfRef(ref, g) map { h =>
              val dupSXY: (Sub[SXY |*| A, B] |*| (SXY |*| A)) -⚬ ((Sub[SXY |*| A, B] |*| SXY) |*| (SXY |*| A)) =
                𝒞.snd(𝒞.fst(dupSub[X, Y]) > 𝒞.assocLR) > 𝒞.assocRL
              val captureSXY: ((Sub[SXY |*| A, B] |*| SXY) |*| (SXY |*| A)) -⚬ (Sub[A, B] |*| (SXY |*| A)) =
                𝒞.fst(captureIntoSub[Sub[X, Y], A, B](ignoreSub[X, Y], dupSub[X, Y]))
              val h1: (Sub[SXY |*| A, B] |*| (SXY |*| A)) -⚬ B =
                dupSXY > captureSXY > 𝒞.xi > h
              Regular(RecFun[-⚬, SXY |*| A, B](h1))
            }
          case CaptureIntoSub(discard, split) =>
            (elimSelfRef(ref, discard), elimSelfRef(ref, split)) match
              case (None, None) => None
              case (Some(d), _) => libretto.lambda.UnhandledCase.raise(s"Recursive call in discarder of the captured expression")
              case (_, Some(s)) => libretto.lambda.UnhandledCase.raise(s"Recursive call in splitter of the captured expression")

          case _: Leaf[A, B] =>
            None
  }

  @tailrec
  private[-⚬] def computeSize(acc: Long, counted: Set[Object], togo: List[(Object, Blueprint[?, ?])]): Long =
    togo match
      case Nil =>
        acc
      case (id, f) :: tail =>
        if (counted.contains(id))
          computeSize(acc, counted, tail)
        else
          val SizeAndRefs(n, refs) = f.sizeAndRefs
          computeSize(acc + n, counted + id, refs.toList ::: tail)
}

/** A representation of Libretto functions. Unlike [[-⚬]], it is a proper blueprint
 * in that it does not exploit cycles in the (Scala-level) object graph.
 */
enum Blueprint[A, B]:
  case Regular(value: Fun[Blueprint, A, B])

  case FunRef(
    id: Object, // XXX: use a proper Id type
    f: Blueprint[A, B],
  )

  case ConstSub[A, B](
    f: Blueprint[A, B],
  ) extends Blueprint[One, Sub[A, B]]

  private[impl] lazy val sizeAndRefs: SizeAndRefs =
    import SizeAndRefs.one

    this match
      case FunRef(id, f) =>
        SizeAndRefs(1, Map(id -> f))
      case ConstSub(f) =>
        one + f.sizeAndRefs
      case Regular(f) =>
        one + f.foldMonoid([X, Y] => (g: Blueprint[X, Y]) => g.sizeAndRefs)

private[impl] case class SizeAndRefs(size: Long, refs: Map[Object, Blueprint[?, ?]]):
  def +(that: SizeAndRefs): SizeAndRefs =
    SizeAndRefs(this.size + that.size, this.refs ++ that.refs)

  def +(n: Int): SizeAndRefs =
    SizeAndRefs(size + n, refs)

private[impl] object SizeAndRefs {
  def apply(n: Int): SizeAndRefs =
    SizeAndRefs(n, Map.empty)

  val one: SizeAndRefs =
    SizeAndRefs(1)

  given Monoid[SizeAndRefs] with
    override def unit: SizeAndRefs = SizeAndRefs(0, Map.empty)
    override def combine(l: SizeAndRefs, r: SizeAndRefs): SizeAndRefs = l + r
}