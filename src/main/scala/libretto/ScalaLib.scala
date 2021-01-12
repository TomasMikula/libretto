package libretto

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
        par(constVal(()), id[Val[A]]) >>> unliftPair >>> mapVal(_._2)
    }

  implicit def junctionNeg[A]: Junction.Negative[Neg[A]] =
    new Junction.Negative[Neg[A]] {
      override def awaitNegFst: Neg[A] -⚬ (Need |*| Neg[A]) =
        contramapNeg[(Unit, A), A](_._2) >>> liftNegPair >>> par(constNeg(()), id[Neg[A]])
    }

  implicit def signalingVal[A]: Signaling.Positive[Val[A]] =
    new Signaling.Positive[Val[A]] {
      override def signalPosFst: Val[A] -⚬ (Done |*| Val[A]) =
        dup[A].>.fst(neglect)
    }

  implicit def signalingNeg[A]: Signaling.Negative[Neg[A]] =
    new Signaling.Negative[Neg[A]] {
      override def signalNegFst: (Need |*| Neg[A]) -⚬ Neg[A] =
        par(inflate[A], id[Neg[A]]) >>> mergeDemands
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
      .bimap(neglect, neglect)            .to[   Done    |+|   Done    ]
  }

  def unliftBoolean: Bool -⚬ Val[Boolean] =
    id[Bool]                              .to[   Done    |+|   Done    ]
      .bimap(constVal(()), constVal(()))  .to[ Val[Unit] |+| Val[Unit] ]
      .>(unliftEither)                    .to[ Val[Either[Unit, Unit]] ]
      .>(mapVal(eitherToBoolean))         .to[      Val[Boolean]       ]

  def maybeToOption[A]: Maybe[Val[A]] -⚬ Val[Option[A]] =
    id[Maybe[Val[A]]]                     .to[    One    |+| Val[A] ]
      .>.left(const(()))                  .to[ Val[Unit] |+| Val[A] ]
      .>(unliftEither)                    .to[ Val[Either[Unit, A]] ]
      .>(mapVal(_.toOption))              .to[ Val[Option[A]]       ]

  def optionToPMaybe[A]: Val[Option[A]] -⚬ PMaybe[Val[A]] =
    id[Val[Option[A]]]                    .to[ Val[Option[      A]] ]
      .>(mapVal(_.toRight(())))           .to[ Val[Either[Unit, A]] ]
      .>(liftEither)                      .to[ Val[Unit] |+| Val[A] ]
      .>.left(dsl.neglect)                .to[   Done    |+| Val[A] ]

  def pMaybeToOption[A]: PMaybe[Val[A]] -⚬ Val[Option[A]] =
    id[PMaybe[Val[A]]]                    .to[   Done    |+| Val[A] ]
      .>.left(constVal(()))               .to[ Val[Unit] |+| Val[A] ]
      .>(unliftEither)                    .to[ Val[Either[Unit, A]] ]
      .>(mapVal(_.toOption))              .to[ Val[Option[A]]       ]

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
}
