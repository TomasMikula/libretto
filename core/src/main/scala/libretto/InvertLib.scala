package libretto

import libretto.lambda.util.SourcePos

object InvertLib {
  def apply(
    coreLib: CoreLib[? <: InvertDSL],
  ): InvertLib[coreLib.type] =
    new InvertLib[coreLib.type](coreLib)
}

class InvertLib[
  CoreLib <: libretto.CoreLib[? <: InvertDSL],
](
  val coreLib: CoreLib,
) {
  import coreLib.dsl.*
  import coreLib.*

  def inversionDuality[A]: Dual[A, -[A]] =
    new Dual[A, -[A]] {
      override val rInvert: (A |*| -[A]) -⚬ One = backvert[A]
      override val lInvert: One -⚬ (-[A] |*| A) = forevert[A]
    }

  // contraFunctorDemand
  given ContraFunctor[-] with {
    override val category =
      coreLib.category

    override def lift[A, B](f: A -⚬ B): -[B] -⚬ -[A] =
      contrapositive(f)
  }

  extension (jp: Junction.Positive.type) {
    def insideInversion[A](using A: Junction.Positive[A]): Junction.Positive[-[A]] =
      Junction.Positive.from {
        λ { case d |*| na =>
          demandTogether(dii(d) |*| na)
            .contramap[A](λ { a =>
              val nd |*| d = constant(forevert[Done])
              nd |*| A.awaitPos(d |*| a)
            })
        }
      }
  }

  extension (jn: Junction.Negative.type) {
    def insideInversion[A](using A: Junction.Negative[A]): Junction.Negative[-[A]] =
      Junction.Negative.from {
        λ { na =>
          na.contramap[-[Need] |*| A](λ { case nn |*| a =>
            val n |*| a1 = A.awaitNeg(a)
            returning(a, n supplyTo nn)
          }) :>> demandSeparately :>> fst(die)
        }
      }
  }

  extension (obj: Unlimited.type) {
    def pool[A](using Signaling.Positive[A]): LList1[A] -⚬ (Unlimited[A |*| -[A]] |*| LList1[A]) =
      Unlimited.poolBy[A, -[A]](forevert[A])
  }

  extension (obj: Endless.type) {
    def pool[A](using Signaling.Positive[A]): LList1[A] -⚬ (Endless[A |*| -[A]] |*| LList1[A]) =
      obj.poolBy[A, -[A]](forevert[A])

    def poolReset[A, B](reset: B -⚬ A)(using
      Signaling.Positive[A]
    ): LList1[A] -⚬ (Endless[A |*| -[B]] |*| LList1[A]) =
      obj.poolBy[A, -[B]](forevert[B] > snd(reset))
  }

  extension [A](a: $[A]) {
    def race[B](using SourcePos, LambdaContext)(b: $[B])(using
      Signaling.Positive[A],
      Signaling.Positive[B],
    ): $[(A |*| B) |+| (A |*| B)] =
      coreLib.race[A, B](a |*| b)

    def race[B](using SourcePos, LambdaContext)(b: ??[B])(using
      Signaling.Positive[A],
      Signaling.Negative[B],
    ): ($[A |+| A], ??[B]) =
      (a :>> notifyPosFst) match {
        case ping |*| a =>
          (notifyNegFst >>: b) match {
            case pong |*| b =>
              (racePair(ping |*| pong.asInput(lInvertPongPing)) switch {
                case Left(?(_))  => injectL(a)
                case Right(?(_)) => injectR(a)
              }, b)
      }
    }

    infix def raceWith[B, C](using SourcePos, LambdaContext)(b: ??[B])(using
      Signaling.Positive[A],
      Signaling.Negative[B],
    )(f: LambdaContext ?=> Either[($[A], ??[B]), ($[A], ??[B])] => $[C]): $[C] = {
      val (aa, bb) = race[B](b)
      aa switch {
        case Left(a)  => f(Left((a, bb)))
        case Right(a) => f(Right((a, bb)))
      }
    }
  }

  extension [A](a: ??[A]) {
    def race[B](using SourcePos, LambdaContext)(b: $[B])(using
      Signaling.Negative[A],
      Signaling.Positive[B],
    ): (??[A |&| A], $[B]) =
      (notifyNegFst >>: a) match {
        case pong |*| a =>
          (b :>> notifyPosFst) match {
            case ping |*| b =>
              ((selectPair >>: (pong |*| ping.asOutput(rInvertPingPong))) choose {
                case Left(one)  => (chooseL >>: a) alsoElim one
                case Right(one) => (chooseR >>: a) alsoElim one
              }, b)
          }
      }

    infix def raceWith[B, C](using SourcePos, LambdaContext)(b: $[B])(using
      Signaling.Negative[A],
      Signaling.Positive[B],
    )(f: LambdaContext ?=> Either[(??[A], $[B]), (??[A], $[B])] => ??[C]): ??[C] = {
      val (aa, bb) = race[B](b)
      aa choose {
        case Left(a)  => f(Left((a, bb)))
        case Right(a) => f(Right((a, bb)))
      }
    }

    def race[B](using SourcePos, LambdaContext)(b: ??[B])(using
      Signaling.Negative[A],
      Signaling.Negative[B],
    ): ??[(A |*| B) |&| (A |*| B)] =
      coreLib.select[A, B] >>: (a |*| b)
  }
}
