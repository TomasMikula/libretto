package libretto.scaletto

import java.util.concurrent.atomic.AtomicLong
import libretto.{CoreLib, InvertLib}
import libretto.lambda.util.SourcePos
import libretto.util.Async
import scala.annotation.targetName
import scala.concurrent.duration.*
import scala.reflect.TypeTest
import scala.util.Random
import scala.annotation.nowarn

object ScalettoLib {
  def apply(
    dsl: Scaletto,
    coreLib: CoreLib[dsl.type],
  )
  : ScalettoLib[dsl.type, coreLib.type] =
    new ScalettoLib(dsl, coreLib)
}

class ScalettoLib[
  DSL <: Scaletto,
  CoreLib <: libretto.CoreLib[DSL],
](
  val dsl: DSL,
  val coreLib: CoreLib with libretto.CoreLib[dsl.type],
) {
  import dsl.*
  import dsl.$.*
  import coreLib.*

  private val invertLib = InvertLib(coreLib)
  import invertLib.*

  object Val {
    def isEq[A](a: A): Val[A] -⚬ (Val[a.type] |+| Val[A]) =
      mapVal[A, Either[a.type, A]] {
        case `a` => Left(a: a.type)
        case x   => Right(x)
      } > liftEither

    def switch[A, B](cases: List[(A, Done -⚬ B)]): Val[A] -⚬ PMaybe[B] =
      cases match {
        case Nil =>
          neglect > PMaybe.empty
        case (a, f) :: tail =>
          Val.isEq(a) > either(
            neglect > f > PMaybe.just,
            switch(tail),
          )
      }
  }

  def const[A](a: A): One -⚬ Val[A] =
    andThen(done, constVal(a))

  given junctionVal[A]: Junction.Positive[Val[A]] =
    new Junction.Positive[Val[A]] {
      override def awaitPosFst: (Done |*| Val[A]) -⚬ Val[A] =
        par(constVal(()), id[Val[A]]) > unliftPair > mapVal(_._2)
    }

  given junctionNeg[A]: Junction.Negative[Neg[A]] with {
    override def awaitNegFst: Neg[A] -⚬ (Need |*| Neg[A]) =
      contramapNeg[(Unit, A), A](_._2) > liftNegPair > par(constNeg(()), id[Neg[A]])
  }

  given signalingVal[A]: Signaling.Positive[Val[A]] =
    new Signaling.Positive[Val[A]] {
      override def notifyPosFst: Val[A] -⚬ (Ping |*| Val[A]) =
        notifyVal
    }

  given signalingNeg[A]: Signaling.Negative[Neg[A]] with {
    override def notifyNegFst: (Pong |*| Neg[A]) -⚬ Neg[A] =
      notifyNeg
  }

  given signalingJunctionPositiveVal[A]: SignalingJunction.Positive[Val[A]] =
    SignalingJunction.Positive.from(
      signalingVal,
      junctionVal,
    )

  given signalingJunctionNegativeNeg[A]: SignalingJunction.Negative[Neg[A]] =
    SignalingJunction.Negative.from(
      signalingNeg,
      junctionNeg,
    )

  given valNegDuality[A]: Dual[Val[A], Neg[A]] with {
    val lInvert: One -⚬ (Neg[A] |*| Val[A]) = promise[A]
    val rInvert: (Val[A] |*| Neg[A]) -⚬ One = fulfill[A]
  }

  given negValDuality[A]: Dual[Neg[A], Val[A]] =
    dualSymmetric(valNegDuality)

  def mergeDemands[A]: (Neg[A] |*| Neg[A]) -⚬ Neg[A] =
    id                                         [                                       Neg[A] |*| Neg[A]   ]
      .>(introFst(promise[A]))              .to[ (Neg[A] |*|        Val[A]      ) |*| (Neg[A] |*| Neg[A])  ]
      .>(assocLR)                           .to[  Neg[A] |*| (      Val[A]        |*| (Neg[A] |*| Neg[A])) ]
      .>.snd.fst(dup)                       .to[  Neg[A] |*| ((Val[A] |*| Val[A]) |*| (Neg[A] |*| Neg[A])) ]
      .>.snd(IXI)                           .to[  Neg[A] |*| ((Val[A] |*| Neg[A]) |*| (Val[A] |*| Neg[A])) ]
      .>.snd(parToOne(fulfill, fulfill))    .to[  Neg[A] |*|                      One                      ]
      .>(elimSnd)                           .to[  Neg[A]                                                   ]

  def delayVal[A](by: Done -⚬ Done): Val[A] -⚬ Val[A] =
    signalPosFst > par(by, id) > awaitPosFst

  def delayVal[A](by: FiniteDuration): Val[A] -⚬ Val[A] =
    delayVal(delay(by))

  def delayRandomMs(minMs: Int, maxMs: Int): Done -⚬ Done =
    constVal(()) > mapVal(_ => Random.between(minMs, maxMs).millis) > delay

  def delayValRandomMs[A](minMs: Int, maxMs: Int): Val[A] -⚬ Val[A] =
    delayVal(delayRandomMs(minMs, maxMs))

  @nowarn("msg=match may not be exhaustive")
  def latestValue[A]: (Val[A] |*| LList[Val[A]]) -⚬ (Endless[Val[A]] |*| Done) = rec { self =>
    λ { case +(a) |*| as =>
      producing { case outAs |*| outDone =>
        (outAs raceWith as) {
          case Left((outAs, as)) =>
            (Endless.fromChoice >>: outAs) switch {
              case Left(end) => // no more reads
                returning(
                  end := one,
                  outDone := LList1.cons(a |*| as) :>> LList1.closeAll,
                )
              case Right(na |*| nas) => // read
                returning(
                  na := a,
                  (nas |*| outDone) := self(a |*| as),
                )
            }
          case Right((outAs, as)) =>
            (outAs |*| outDone) :=
              LList.uncons(as) switch {
                case Left(?(_)) => // no more writes
                  a :>> Endless.unfold(dup) :>> snd(neglect)
                case Right(a1 |*| as) => // write
                  self((a1 waitFor neglect(a)) |*| as)
              }
        }
      }
    }
  }

  given closeableCosemigroupVal[A]: CloseableCosemigroup[Val[A]] with {
    override def close : Val[A] -⚬ Done                = dsl.neglect
    override def split : Val[A] -⚬ (Val[A] |*| Val[A]) = dup
  }

  given [A]: NMonoid[Neg[A]] with {
    def unit    :                Need -⚬ Neg[A] = inflate
    def combine : (Neg[A] |*| Neg[A]) -⚬ Neg[A] = mergeDemands
  }

  private val eitherToBoolean: Either[Unit, Unit] => Boolean = {
    case Left(())  => true
    case Right(()) => false
  }

  private val booleanToEither: Boolean => Either[Unit, Unit] = {
    case true => Left(())
    case false => Right(())
  }

  def liftBoolean: Val[Boolean] -⚬ Bool = {
    id                                       [ Val[Boolean]            ]
      .>(mapVal(booleanToEither))         .to[ Val[Either[Unit, Unit]] ]
      .>(liftEither)                      .to[ Val[Unit] |+| Val[Unit] ]
      .>(either(
        neglect > Bool.constTrue,
        neglect > Bool.constFalse,
      ))                                  .to [          Bool          ]
  }

  def unliftBoolean: Bool -⚬ Val[Boolean] =
    Bool.switch(
      caseTrue = constVal(true),
      caseFalse = constVal(false),
    )

  def maybeToOption[A]: Maybe[Val[A]] -⚬ Val[Option[A]] =
    Maybe.toEither[Val[A]]                .to[    One    |+| Val[A] ]
      .>.left(const(()))                  .to[ Val[Unit] |+| Val[A] ]
      .>(unliftEither)                    .to[ Val[Either[Unit, A]] ]
      .>(mapVal(_.toOption))              .to[ Val[Option[A]]       ]

  def optionToPMaybe[A]: Val[Option[A]] -⚬ PMaybe[Val[A]] =
    id                                       [ Val[Option[      A]] ]
      .>(mapVal(_.toRight(())))           .to[ Val[Either[Unit, A]] ]
      .>(liftEither)                      .to[ Val[Unit] |+| Val[A] ]
      .>.left(dsl.neglect)                .to[   Done    |+| Val[A] ]
      .>(PMaybe.fromEither)               .to[     PMaybe[Val[A]]   ]

  def pMaybeToOption[A]: PMaybe[Val[A]] -⚬ Val[Option[A]] =
    PMaybe.switch(
      caseNone = constVal(None),
      caseSome = mapVal(Some(_)),
    )

  def liftBipredicate[A, B](p: (A, B) => Boolean): (Val[A] |*| Val[B]) -⚬ Bool =
    id                                       [ Val[A] |*| Val[B] ]
      .>(unliftPair)                      .to[   Val[(A, B)]     ]
      .>(mapVal(p.tupled))                .to[   Val[Boolean]    ]
      .>(liftBoolean)                     .to[       Bool        ]

  def isLt[A](using ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.lt)

  def isLteq[A](using ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.lteq)

  def isGt[A](using ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.gt)

  def isGteq[A](using ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.gteq)

  def isEq[A](using ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.equiv)

  def testByVals[A, B, K](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
    pred: (K, K) => Boolean,
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) = {
    testBy(aKey, bKey, liftBipredicate(pred))
  }

  def ltBy[A, B, K](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )(using
    ord: Ordering[K],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    testByVals(aKey, bKey, ord.lt)

  def lteqBy[A, B, K](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )(using
    ord: Ordering[K],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    testByVals(aKey, bKey, ord.lteq)

  def gtBy[A, B, K](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )(using
    ord: Ordering[K],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    testByVals(aKey, bKey, ord.gt)

  def gteqBy[A, B, K](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )(using
    ord: Ordering[K],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    testByVals(aKey, bKey, ord.gteq)

  def equivBy[A, B, K](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )(using
    ord: Ordering[K],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    testByVals(aKey, bKey, ord.equiv)

  def sortBy[A, B, K: Ordering](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )
  : (A |*| B) -⚬ ((A |*| B) |+| (B |*| A)) =
    lteqBy(aKey, bKey).>.right(swap)

  given [A : Ordering]: Comparable[Val[A], Val[A]] with {
    import coreLib.given, Compared.*, Either as ⊻

    private val scalaCompare: ((A, A)) => ((A, A) ⊻ ((A, A) ⊻ (A, A))) =
      { (a1, a2) =>
        Ordering[A].compare(a1, a2) match {
          case i if i < 0 => Left((a1, a2))
          case 0          => Right(Left((a1, a2)))
          case i if i > 0 => Right(Right((a1, a2)))
        }
      }

    override def compare: (Val[A] |*| Val[A]) -⚬ Compared[Val[A], Val[A]] =
      id                                                           [              Val[A] |*| Val[A]                                        ]
        .>(unliftPair)                                          .to[ Val[               (A, A)                                           ] ]
        .>(mapVal(scalaCompare))                                .to[ Val[(A   ,      A) Either (  (A   ,      A) Either   (A   ,      A))] ]
        .>(liftEither).>.right(liftEither)                      .to[ Val[(A   ,      A)] |+| (Val[(A   ,      A)] |+| Val[(A   ,      A)]) ]
        .>(|+|.bimap(liftPair, |+|.bimap(liftPair, liftPair)))  .to[ (Val[A] |*| Val[A]) |+| ((Val[A] |*| Val[A]) |+| (Val[A] |*| Val[A])) ]
        .>(either(lt, either(equiv, gt)))                       .to[                Compared[Val[A], Val[A]]                               ]
  }

  def constList[A](as: List[A]): One -⚬ LList[Val[A]] =
    LList.fromList(as.map(const(_)))

  def constListOf[A](as: A*): One -⚬ LList[Val[A]] =
    constList(as.toList)

  def constListOf1[A](a: A, as: A*): Done -⚬ LList[Val[A]] =
    constList1(a, as.toList) > LList1.toLList

  def liftScalaList1[A]: Val[::[A]] -⚬ LList1[Val[A]] = rec { self =>
    mapVal[::[A], Either[A, (A, ::[A])]] {
      case a0 :: Nil => Left(a0)
      case a0 :: a1 :: as => Right((a0, ::(a1, as)))
    } > liftEither > either(
      LList1.singleton,
      liftPair > snd(self) > LList1.cons1,
    )
  }

  def toScalaList[A]: LList[Val[A]] -⚬ Val[List[A]] = rec { self =>
    LList.switch(
      caseNil  = const(List.empty[A]),
      caseCons = par(id, self) > unliftPair > mapVal(_ :: _),
    )
  }

  def constList1[A](a: A, as: List[A]): Done -⚬ LList1[Val[A]] =
    LList1.from(constVal(a), as.map(constVal))

  def constList1[A](as: ::[A]): Done -⚬ LList1[Val[A]] = {
    val h :: t = as
    constList1(h, t)
  }

  def constList1Of[A](a: A, as: A*): Done -⚬ LList1[Val[A]] =
    constList1(a, as.toList)

  def toScalaList1[A]: LList1[Val[A]] -⚬ Val[::[A]] =
    rec { self =>
      LList1.switch(
        case1 = mapVal(::(_, Nil)),
        caseN = snd(self) > unliftPair > mapVal { case (h, t) => ::(h, t) },
      )
    }

  /** Create a resource that is just a (potentially) mutable value which does not need any cleanup.
    *
    * @param init function that initializes the (potentially) mutable value from an immutable one.
    */
  def mVal[A, R](init: A => R): Val[A] -⚬ Res[R] =
    acquire[A, R, Unit](a => (init(a), ()), release = None) > effectWr((_, _) => ())

  /** Variant of [[acquire]] that does not produce extra output in addition to the resource. */
  def acquire0[A, R](
    acquire: A => R,
    release: Option[R => Unit],
  ): Val[A] -⚬ Res[R] =
    dsl.acquire[A, R, Unit](a => (acquire(a), ()), release) > effectWr((_, _) => ())

  /** Variant of [[acquireAsync]] that does not produce extra output in addition to the resource. */
  def acquireAsync0[A, R](
    acquire: A => Async[R],
    release: Option[R => Async[Unit]],
  ): Val[A] -⚬ Res[R] =
    dsl.acquireAsync[A, R, Unit](a => acquire(a).map((_, ())), release) > effectWr((_, _) => ())

  /** Variant of [[release]] that does not take additional input. */
  def release0[R, B](release: R => B): Res[R] -⚬ Val[B] =
    id[Res[R]] > introSnd(const(())) > dsl.release((r, _) => release(r))

  /** Variant of [[releaseAsync]] that does not take additional input. */
  def releaseAsync0[R, B](release: R => Async[B]): Res[R] -⚬ Val[B] =
    id[Res[R]] > introSnd(const(())) > dsl.releaseAsync((r, _) => release(r))

  def effectRd[R, B](f: ScalaFun[R, B]): Res[R] -⚬ (Res[R] |*| Val[B]) =
    id[Res[R]] > introSnd(const(())) > effect(f.adapt[(R, Unit), B](_._1, identity))

  def effectRd[R, B](f: R => B): Res[R] -⚬ (Res[R] |*| Val[B]) =
    effectRd(ScalaFun(f))

  /** Variant of [[effect]] that does not take additional input and does not produce additional output. */
  def effect0[R](f: R => Unit): Res[R] -⚬ Res[R] =
    id[Res[R]] > introSnd(const(())) > effectWr((r, _) => f(r))

  /** Variant of [[effectAsync]] that does not take additional input and does not produce additional output. */
  def effectAsync0[R](f: R => Async[Unit]): Res[R] -⚬ Res[R] =
    id[Res[R]] > introSnd(const(())) > effectWrAsync((r, _) => f(r))

  def tryEffectAcquireWr[R, A, S, E](
    f: ScalaFun[(R, A), Either[E, S]],
    release: Option[ScalaFun[S, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| (Val[E] |+| Res[S])) =
    tryEffectAcquire[R, A, S, Unit, E](
      f.adaptPost(_.map(s => (s, ()))),
      release,
    ) > snd(|+|.rmap(effectWr((_, _) => ())))

  /** Variant of [[transformResource]] that does not take additional input and does not produce additional output. */
  def transformResource0[R, S](f: R => S, release: Option[S => Unit]): Res[R] -⚬ Res[S] =
    id[Res[R]] > introSnd(const(())) > transformResource((r, u) => (f(r), u), release) > effectWr((_, _) => ())

  /** Variant of [[transformResourceAsync]] that does not take additional input and does not produce additional output. */
  def transformResourceAsync0[R, S](f: R => Async[S], release: Option[S => Async[Unit]]): Res[R] -⚬ Res[S] =
    id[Res[R]] > introSnd(const(())) > transformResourceAsync((r, u) => f(r).map((_, u)), release) > effectWr((_, _) => ())

  def splitResource0[R, S, T](
    f: ScalaFun[R, (S, T)],
    release1: Option[ScalaFun[S, Unit]],
    release2: Option[ScalaFun[T, Unit]],
  ): Res[R] -⚬ (Res[S] |*| Res[T]) = {
    val f1: ScalaFun[(R, Unit), (S, T, Unit)] =
      ScalaFun.adapt(f)({ case (r, ()) => r }, { case (s, t) => (s, t, ()) })
    id[Res[R]]
      .>(introSnd(const(())))
      .>(splitResource(f1, release1, release2))
      .>(assocLR)
      .>.snd(effectWr((_, _) => ()))
  }

  def splitResource0[R, S, T](
    f: R => (S, T),
    release1: Option[S => Unit],
    release2: Option[T => Unit],
  ): Res[R] -⚬ (Res[S] |*| Res[T]) =
    splitResource0(
      ScalaFun(f),
      release1.map(ScalaFun(_)),
      release2.map(ScalaFun(_)),
    )


  def splitResourceAsync0[R, S, T](
    f: R => Async[(S, T)],
    release1: Option[S => Async[Unit]],
    release2: Option[T => Async[Unit]],
  ): Res[R] -⚬ (Res[S] |*| Res[T]) =
    splitResource0(
      ScalaFun.async(f),
      release1.map(ScalaFun.async(_)),
      release2.map(ScalaFun.async(_)),
    )

  extension [R](r: $[Res[R]])(using LambdaContext) {
    @targetName("releaseResourceWhen")
    def releaseWhen(d: $[Done])(using SourcePos): $[Done] =
      (r |*| constVal(())(d)) :>> effectWr((_, _) => ()) :>> release

    def releaseOnPing(p: $[Ping])(using SourcePos): $[Done] =
      releaseWhen(strengthenPing(p))
  }

  opaque type RefCounted[R] = Res[RefCounted.Repr[R]]

  object RefCounted {
    private[ScalettoLib] type Repr[R] = (R, ScalaFun[R, Unit], AtomicLong)

    def acquire[A, R, B](
      acquire: ScalaFun[A, (R, B)],
      release: ScalaFun[R, Unit],
    ): Val[A] -⚬ (RefCounted[R] |*| Val[B]) =
      dsl.acquire[A, (R, ScalaFun[R, Unit], AtomicLong), B](
        acquire = acquire.adaptPost { case (r, b) =>
          ((r, release, new AtomicLong(1L)), b)
        },
        release = Some(releaseFn[R]),
      )

    def acquire[A, R, B](acquire: A => (R, B), release: R => Unit): Val[A] -⚬ (RefCounted[R] |*| Val[B]) =
      RefCounted.acquire(ScalaFun(acquire), ScalaFun(release))

    def acquire0[A, R](acquire: A => R, release: R => Unit): Val[A] -⚬ RefCounted[R] =
      RefCounted.acquire[A, R, Unit](a => (acquire(a), ()), release) > effectWr((_, _) => ())

    def release[R]: RefCounted[R] -⚬ Done =
      dsl.release

    def releaseWhenDone[R]: (Done |*| RefCounted[R]) -⚬ Done =
      λ { case done |*| res =>
        (res |*| constVal(())(done))
        :>> effectWr((_, _) => ())
        :>> release
      }

    def releaseOnPing[R]: (Ping |*| RefCounted[R]) -⚬ Done =
      fst(strengthenPing) > releaseWhenDone

    def dupRef[R]: RefCounted[R] -⚬ (RefCounted[R] |*| RefCounted[R]) =
      splitResource0(
        ScalaFun[Repr[R], (Repr[R], Repr[R])] {
          case rc @ (_, _, n) =>
            n.incrementAndGet()
            (rc, rc)
        },
        Some(releaseFn[R]),
        Some(releaseFn[R]),
      )

    def effect[R, A, B](f: (R, A) => B): (RefCounted[R] |*| Val[A]) -⚬ (RefCounted[R] |*| Val[B]) =
      dsl.effect((rn, a) => f(rn._1, a))

    def effectAsync[R, A, B](f: (R, A) => Async[B]): (RefCounted[R] |*| Val[A]) -⚬ (RefCounted[R] |*| Val[B]) =
      dsl.effectAsync((rn, a) => f(rn._1, a))

    def effectRd[R, B](f: ScalaFun[R, B]): RefCounted[R] -⚬ (RefCounted[R] |*| Val[B]) =
      ScalettoLib.this.effectRd(f.adapt[Repr[R], B](_._1, identity))

    def effectRdAcquire[R, B](
      f: ScalaFun[R, B],
      release: Option[ScalaFun[B, Unit]],
    ): RefCounted[R] -⚬ (RefCounted[R] |*| Res[B]) = {
      val f1: ScalaFun[Repr[R], (Repr[R], B)] =
        f.adaptWith[Repr[R], Repr[R], (Repr[R], B)](
          r => (r, r._1),
          (r, b) => (r, b),
        )
      splitResource0(
        f1,
        release1 = Some(releaseFn[R]),
        release2 = release,
      )
    }

    private def releaseFn[R]: ScalaFun[(R, ScalaFun[R, Unit], AtomicLong), Unit] =
      ScalaFun.eval[R, Unit]
        .adaptPre { case (r, release, n) =>
          n.decrementAndGet match {
            case 0 =>
              // no more references exist, release
              (release, r)
            case i if i > 0 =>
              // there are remaining references, do nothing
              (ScalaFun(identity), r)
            case i =>
              assert(false, s"Bug: reached negative number ($i) of references to $r")
          }
        }
  }

  def putStr: Val[String] -⚬ Done =
    blocking[String, Unit](Console.out.print(_)) > neglect

  def putStr(s: String): Done -⚬ Done =
    constVal(s) > putStr

  def printLine: Val[String] -⚬ Done =
    blocking[String, Unit](Console.out.println(_)) > neglect

  def printLine(s: String): Done -⚬ Done =
    constVal(s) > printLine

  def printLine[A](f: A => String): Val[A] -⚬ Done =
    mapVal(f) > printLine

  def alsoPrintLine: Val[String] -⚬ Val[String] =
    dup > fst(printLine) > awaitPosFst

  def alsoPrintLine[A](f: A => String): Val[A] -⚬ Val[A] =
    dup > fst(mapVal(f) > printLine) > awaitPosFst

  def alsoPrintLine[A](s: String)(using S: Signaling.Positive[A], J: Junction.Positive[A]): A -⚬ A =
    S.signalPosFst > fst(printLine(s)) > J.awaitPosFst

  def readLine: Done -⚬ Val[String] =
    constVal(()) > blocking[Unit, String](_ => Console.in.readLine())

  extension [A](a: $[Val[A]])(using LambdaContext) {
    def **[B](b: $[Val[B]])(using SourcePos): $[Val[(A, B)]] =
      unliftPair(a |*| b)

    @deprecated("Renamed to **")
    def *[B](b: $[Val[B]])(using SourcePos): $[Val[(A, B)]] =
      a ** b
  }

  object ** {
    def unapply[A, B](ab: $[Val[(A, B)]])(using SourcePos, LambdaContext): ($[Val[A]], $[Val[B]]) =
      val a |*| b = ab > liftPair
      (a, b)
  }

  def decrement: Val[Int] -⚬ (Done |+| Val[Int]) =
    mapVal[Int, Either[Unit, Int]](n => if (n > 0) Right(n-1) else Left(()))
    > liftEither
    > (|+|.lmap(neglect))
}
