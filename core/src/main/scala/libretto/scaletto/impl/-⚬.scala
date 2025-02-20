package libretto.scaletto.impl

import libretto.lambda.{
  ClosedSymmetricMonoidalCategory,
  CocartesianNAryCategory,
  CocartesianSemigroupalCategory,
  Distribution,
  DistributionNAry,
  Member,
  SemigroupalCategory,
  SinkNAryNamed,
}
import libretto.lambda.util.{Exists, SourcePos, TypeEq, Validated}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.util.Validated.{Valid, invalid}
import scala.annotation.tailrec

import phantoms.*

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

  val cocatN: CocartesianNAryCategory[-⚬, OneOf, ||, ::] =
    new CocartesianNAryCategory[-⚬, OneOf, ||, ::] {
      override def inject[Label, A, Cases](
        i: Member[||, ::, Label, A, Cases],
      ): A -⚬ OneOf[Cases] =
        Regular(OneOfInject(i))

      override def handle[Cases, R](
        handlers: SinkNAryNamed[-⚬, ||, ::, Cases, R],
      ): OneOf[Cases] -⚬ R =
        Regular(OneOfHandle(handlers))
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

  val distributionN: DistributionNAry[-⚬, |*|, OneOf, ||, ::] =
    new DistributionNAry[-⚬, |*|, OneOf, ||, ::] {
      override val cat: SemigroupalCategory[-⚬, |*|] =
        𝒞

      override def distLR[A, Cases](
        ev: DistributionNAry.DistLR[|*|, ||, ::, A, Cases],
      ): (A |*| OneOf[Cases]) -⚬ OneOf[ev.Out] =
        Regular(DistributeNAryLR(ev))

      override def distRL[B, Cases](
        ev: DistributionNAry.DistRL[|*|, ||, ::, B, Cases],
      ): (OneOf[Cases] |*| B) -⚬ OneOf[ev.Out] =
        Regular(DistributeNAryRL(ev))
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
            case OneOfHandle(hs) => OneOfHandle(hs.translate([x, y] => h => fromBlueprint(h)))
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
          case f: OneOfHandle[arr, cases, r] =>
            type Arr[P, Q] = Either[P -⚬ Q, (Sub[X, Y] |*| P) -⚬ Q]
            val hs = f.handlers.translate[Arr]([x, y] => (h: x -⚬ y) => elimSelfRef(ref, h).toRight(h))
            if (hs.forall([x, y] => h => h.isLeft)) {
              None
            } else {
              val hs1 =
                hs.translate[[x, y] =>> (Sub[X, Y] |*| x) -⚬ y](
                  [x, y] => h => h match {
                    case Right(h) => h
                    case Left(h) => 𝒞.elimFst(ignoreSub) > h
                  }
                )

              def go[Ps](
                hs: SinkNAryNamed[[p, q] =>> (Sub[X, Y] |*| p) -⚬ q, ||, ::, Ps, B],
              ): Exists[[Qs] =>> (
                DistributionNAry.DistLR[|*|, ||, ::, Sub[X, Y], Ps] { type Out = Qs },
                SinkNAryNamed[-⚬, ||, ::, Qs, B],
              )] =
                hs match
                  case s: SinkNAryNamed.Single[arr, sep, of, l, p, b] =>
                    Exists((
                      DistributionNAry.DistLR.Single[|*|, ||, ::, Sub[X, Y], l, p](s.label),
                      SinkNAryNamed.Single(s.label, s.h)
                    ))
                  case s: SinkNAryNamed.Snoc[arr, sep, of, init, l, z, b] =>
                    go(s.init) match
                      case Exists.Some((d, init)) =>
                        Exists((
                          DistributionNAry.DistLR.Snoc[|*|, ||, ::, Sub[X, Y], init, l, z, d.Out](d, s.label),
                          SinkNAryNamed.Snoc(init, s.label, s.last)
                        ))

              go(hs1) match
                case Exists.Some((d, s)) =>
                  Some(distributionN.distLR(d) > cocatN.handle(s))
            }
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
