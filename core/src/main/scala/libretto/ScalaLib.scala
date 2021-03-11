package libretto

import java.util.concurrent.atomic.AtomicLong

object ScalaLib {
  def apply(
    dsl: ScalaDSL,
    coreLib: CoreLib[dsl.type],
  )
  : ScalaLib[dsl.type, coreLib.type] =
    new ScalaLib(dsl, coreLib)
}

class ScalaLib[
  DSL <: ScalaDSL,
  CoreLib <: libretto.CoreLib[DSL],
](
  val dsl: DSL,
  val coreLib: CoreLib with libretto.CoreLib[dsl.type],
) {
  import dsl._
  import coreLib._

  def const[A](a: A): One -⚬ Val[A] =
    andThen(done, constVal(a))

  implicit def junctionVal[A]: Junction.Positive[Val[A]] =
    new Junction.Positive[Val[A]] {
      override def awaitPosFst: (Done |*| Val[A]) -⚬ Val[A] =
        par(constVal(()), id[Val[A]]) > unliftPair > mapVal(_._2)
    }

  implicit def junctionNeg[A]: Junction.Negative[Neg[A]] =
    new Junction.Negative[Neg[A]] {
      override def awaitNegFst: Neg[A] -⚬ (Need |*| Neg[A]) =
        contramapNeg[(Unit, A), A](_._2) > liftNegPair > par(constNeg(()), id[Neg[A]])
    }

  implicit def signalingVal[A]: Signaling.Positive[Val[A]] =
    new Signaling.Positive[Val[A]] {
      override def signalPosFst: Val[A] -⚬ (Done |*| Val[A]) =
        dup[A].>.fst(neglect)
    }

  implicit def signalingNeg[A]: Signaling.Negative[Neg[A]] =
    new Signaling.Negative[Neg[A]] {
      override def signalNegFst: (Need |*| Neg[A]) -⚬ Neg[A] =
        par(inflate[A], id[Neg[A]]) > mergeDemands
    }

  implicit def signalingJunctionPositiveVal[A]: SignalingJunction.Positive[Val[A]] =
    SignalingJunction.Positive.from(
      signalingVal,
      junctionVal,
    )

  implicit def signalingJunctionNegativeNeg[A]: SignalingJunction.Negative[Neg[A]] =
    SignalingJunction.Negative.from(
      signalingNeg[A],
      junctionNeg[A],
    )

  implicit def valNegDuality[A]: Dual[Val[A], Neg[A]] =
    new Dual[Val[A], Neg[A]] {
      val lInvert: One -⚬ (Neg[A] |*| Val[A]) = promise[A]
      val rInvert: (Val[A] |*| Neg[A]) -⚬ One = fulfill[A]
    }

  implicit def negValDuality[A]: Dual[Neg[A], Val[A]] =
    dualSymmetric(valNegDuality)

  def mergeDemands[A]: (Neg[A] |*| Neg[A]) -⚬ Neg[A] =
    id                                         [                                       Neg[A] |*| Neg[A]   ]
      .introFst(promise[A])                 .to[ (Neg[A] |*|        Val[A]      ) |*| (Neg[A] |*| Neg[A])  ]
      .assocLR                              .to[  Neg[A] |*| (      Val[A]        |*| (Neg[A] |*| Neg[A])) ]
      .>.snd.fst(dup)                       .to[  Neg[A] |*| ((Val[A] |*| Val[A]) |*| (Neg[A] |*| Neg[A])) ]
      .>.snd(IXI)                           .to[  Neg[A] |*| ((Val[A] |*| Neg[A]) |*| (Val[A] |*| Neg[A])) ]
      .>.snd(parToOne(fulfill, fulfill))    .to[  Neg[A] |*|                      One                      ]
      .elimSnd                              .to[  Neg[A]                                                   ]

  implicit def pComonoidVal[A]: PComonoid[Val[A]] =
    new PComonoid[Val[A]] {
      def counit : Val[A] -⚬ Done                = dsl.neglect
      def split  : Val[A] -⚬ (Val[A] |*| Val[A]) = dup
    }

  implicit def nMonoidNeg[A]: NMonoid[Neg[A]] =
    new NMonoid[Neg[A]] {
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
      .either(
        neglect > Bool.constTrue,
        neglect > Bool.constFalse,
      )                                   .to [          Bool          ]
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
      .either(PMaybe.empty, PMaybe.just)  .to[     PMaybe[Val[A]]   ]

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

  def isLt[A](implicit ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.lt)

  def isLteq[A](implicit ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.lteq)

  def isGt[A](implicit ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.gt)

  def isGteq[A](implicit ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.gteq)

  def isEq[A](implicit ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
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
  )(implicit
    ord: Ordering[K],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    testByVals(aKey, bKey, ord.lt)

  def lteqBy[A, B, K](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )(implicit
    ord: Ordering[K],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    testByVals(aKey, bKey, ord.lteq)

  def gtBy[A, B, K](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )(implicit
    ord: Ordering[K],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    testByVals(aKey, bKey, ord.gt)

  def gteqBy[A, B, K](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )(implicit
    ord: Ordering[K],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    testByVals(aKey, bKey, ord.gteq)

  def equivBy[A, B, K](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )(implicit
    ord: Ordering[K],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    testByVals(aKey, bKey, ord.equiv)

  def sortBy[A, B, K: Ordering](
    aKey: Getter[A, Val[K]],
    bKey: Getter[B, Val[K]],
  )
  : (A |*| B) -⚬ ((A |*| B) |+| (B |*| A)) =
    lteqBy(aKey, bKey).>.right(swap)

  implicit def comparableVal[A](implicit A: Ordering[A]): Comparable[Val[A], Val[A]] =
    new Comparable[Val[A], Val[A]] {
      import coreLib.Compared._

      private val scalaCompare: ((A, A)) => ((A, A) Either ((A, A) Either (A, A))) =
        { (a1, a2) =>
          A.compare(a1, a2) match {
            case i if i < 0 => Left((a1, a2))
            case 0          => Right(Left((a1, a2)))
            case i if i > 0 => Right(Right((a1, a2)))
          }
        }

      override def compare: (Val[A] |*| Val[A]) -⚬ Compared[Val[A], Val[A]] =
        id                                                   [              Val[A] |*| Val[A]                                        ]
          .>(unliftPair)                                  .to[ Val[               (A, A)                                           ] ]
          .>(mapVal(scalaCompare))                        .to[ Val[(A   ,      A) Either (  (A   ,      A) Either   (A   ,      A))] ]
          .>(liftEither).>.right(liftEither)              .to[ Val[(A   ,      A)] |+| (Val[(A   ,      A)] |+| Val[(A   ,      A)]) ]
          .bimap(liftPair, |+|.bimap(liftPair, liftPair)) .to[ (Val[A] |*| Val[A]) |+| ((Val[A] |*| Val[A]) |+| (Val[A] |*| Val[A])) ]
          .either(lt, either(equiv, gt))                  .to[                Compared[Val[A], Val[A]]                               ]
    }

  def constList[A](as: List[A]): One -⚬ LList[Val[A]] =
    LList.fromList(as.map(const(_)))

  def constListOf[A](as: A*): One -⚬ LList[Val[A]] =
    constList(as.toList)

  def toScalaList[A]: LList[Val[A]] -⚬ Val[List[A]] = rec { self =>
    LList.switch(
      caseNil  = const(List.empty[A]),
      caseCons = par(id, self) > unliftPair > mapVal(_ :: _),
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
    id[Res[R]].introSnd(const(())) > dsl.release((r, _) => release(r))

  /** Variant of [[releaseAsync]] that does not take additional input. */
  def releaseAsync0[R, B](release: R => Async[B]): Res[R] -⚬ Val[B] =
    id[Res[R]].introSnd(const(())) > dsl.releaseAsync((r, _) => release(r))

  def effectRd[R, B](f: R => B): Res[R] -⚬ (Res[R] |*| Val[B]) =
    id[Res[R]].introSnd(const(())) > effect((r, _) => f(r))

  /** Variant of [[effect]] that does not take additional input and does not produce additional output. */
  def effect0[R](f: R => Unit): Res[R] -⚬ Res[R] =
    id[Res[R]].introSnd(const(())) > effectWr((r, _) => f(r))

  /** Variant of [[effectAsync]] that does not take additional input and does not produce additional output. */
  def effectAsync0[R](f: R => Async[Unit]): Res[R] -⚬ Res[R] =
    id[Res[R]].introSnd(const(())) > effectWrAsync((r, _) => f(r))

  /** Variant of [[transformResource]] that does not take additional input and does not produce additional output. */
  def transformResource0[R, S](f: R => S, release: Option[S => Unit]): Res[R] -⚬ Res[S] =
    id[Res[R]].introSnd(const(())) > transformResource((r, u) => (f(r), u), release) > effectWr((_, _) => ())

  /** Variant of [[transformResourceAsync]] that does not take additional input and does not produce additional output. */
  def transformResourceAsync0[R, S](f: R => Async[S], release: Option[S => Async[Unit]]): Res[R] -⚬ Res[S] =
    id[Res[R]].introSnd(const(())) > transformResourceAsync((r, u) => f(r).map((_, u)), release) > effectWr((_, _) => ())

  def splitResource0[R, S, T](
    f: R => (S, T),
    release1: Option[S => Unit],
    release2: Option[T => Unit],
  ): Res[R] -⚬ (Res[S] |*| Res[T]) =
    id[Res[R]]
      .introSnd(const(()))
      .>(splitResource((r, u) => { val (s, t) = f(r); (s, t, u) }, release1, release2))
      .assocLR
      .>.snd(effectWr((_, _) => ()))


  def splitResourceAsync0[R, S, T](
    f: R => Async[(S, T)],
    release1: Option[S => Async[Unit]],
    release2: Option[T => Async[Unit]],
  ): Res[R] -⚬ (Res[S] |*| Res[T]) =
    id[Res[R]]
      .introSnd(const(()))
      .>(splitResourceAsync((r, u) => { f(r) map { case (s, t) => (s, t, u) } }, release1, release2))
      .assocLR
      .>.snd(effectWr((_, _) => ()))

  opaque type RefCounted[R] = Res[(R, R => Unit, AtomicLong)]

  object RefCounted {
    def acquire[A, R, B](acquire: A => (R, B), release: R => Unit): Val[A] -⚬ (RefCounted[R] |*| Val[B]) =
      dsl.acquire[A, (R, R => Unit, AtomicLong), B](
        acquire = { a =>
          val (r, b) = acquire(a)
          ((r, release, new AtomicLong(1L)), b)
        },
        release = Some(releaseFn[R]),
      )

    def acquire0[A, R](acquire: A => R, release: R => Unit): Val[A] -⚬ RefCounted[R] =
      RefCounted.acquire[A, R, Unit](a => (acquire(a), ()), release) > effectWr((_, _) => ())

    def release[R]: RefCounted[R] -⚬ Done =
      dsl.release

    def dupRef[R]: RefCounted[R] -⚬ (RefCounted[R] |*| RefCounted[R]) =
      splitResource0(
        { case rc @ (_, _, n) =>
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

    private def releaseFn[R]: ((R, R => Unit, AtomicLong)) => Unit =
      { case (r, release, n) =>
        n.decrementAndGet match {
          case 0 =>
            // no more references exist, release
            release(r)
          case i if i > 0 =>
            // there are remaining references, do nothing
          case i =>
            assert(false, s"Bug: reached negative number ($i) of references to $r")
        }
      }
  }

  def printLine: Val[String] -⚬ Done =
    blocking[String, Unit](Console.out.println(_)) > neglect

  def printLine(s: String): Done -⚬ Done =
    constVal(s) > printLine

  def readLine: Done -⚬ Val[String] =
    constVal(()) > blocking[Unit, String](_ => Console.in.readLine())
}
