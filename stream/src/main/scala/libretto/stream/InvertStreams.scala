package libretto.stream

import libretto.{InvertDSL, CoreLib}
import libretto.util.∀

object InvertStreams {
  def apply(
    dsl: InvertDSL,
    lib: CoreLib[dsl.type],
  )
  : InvertStreams[dsl.type, lib.type] =
    new InvertStreams(dsl, lib)
}

class InvertStreams[DSL <: InvertDSL, Lib <: CoreLib[DSL]](
  override val dsl: DSL,
  override val lib: Lib with CoreLib[dsl.type],
) extends CoreStreams[DSL, Lib](dsl, lib) {
  import dsl._
  import dsl.$._
  import lib._

  type Drain[A] = StreamLeader[Need, -[A]]
  type Sink[A]  = StreamFollower[Need, -[A]]

  object Drain {
    type Pulling[A] = Need |&| (-[A] |*| Drain[A])

    def close[A]: Drain[A] -⚬ Need =
      StreamLeader.switch(id, chooseL)

    def closed[A]: Need -⚬ Drain[A] =
      StreamLeader.closed[Need, -[A]]

    def pulling[A]: Pulling[A] -⚬ Drain[A] =
      StreamLeader.next[Need, -[A]]

    def switch[A, R](
      onClose: Need -⚬ R,
      onPull: Pulling[A] -⚬ R,
    ): Drain[A] -⚬ R =
      StreamLeader.switch(onClose, onPull)

    def toEither[A]: Drain[A] -⚬ (Need |+| Pulling[A]) =
      StreamLeader.unpack

    def fromEither[A]: (Need |+| Pulling[A]) -⚬ Drain[A] =
      StreamLeader.pack

    def onCloseAwait[A]: (Done |*| Drain[A]) -⚬ Drain[A] = rec { self =>
      λ { case (d |*| drain) =>
        toEither(drain) switch {
          case Left(closing) =>
            Drain.closed(needAbsorbDone(closing |*| d))
          case Right(pulling) =>
            Drain.pulling(Pulling.onCloseAwait0(self)(d |*| pulling))
        }
      }
    }

    object Pulling {
      def create[S, A](
        caseClose:    S -⚬ Need,
        caseWarrant:  S -⚬ (-[A] |*| Drain[A]),
      ): S -⚬ Pulling[A] =
        choice(caseClose, caseWarrant)

      def close[A]: Pulling[A] -⚬ Need =
        chooseL

      def warrant[A]: Pulling[A] -⚬ (-[A] |*| Drain[A]) =
        chooseR

      private[Drain] def onCloseAwait0[A](
        drainAwait: (Done |*| Drain[A]) -⚬ Drain[A],
      ): (Done |*| Pulling[A]) -⚬ Pulling[A] =
        create(
          caseClose   = λ { case (d |*| p) => needAbsorbDone(close(p) |*| d) },
          caseWarrant = snd(warrant) > XI > snd(drainAwait),
        )
    }

    private def needAbsorbDone: (Need |*| Done) -⚬ Need =
      fst(joinNeed) > assocLR > elimSnd(swap > rInvertSignal)
  }

  def rInvertDrain[A]: (Drain[A] |*| LPollable[A]) -⚬ One =
    rInvertLeader(swap > rInvertSignal, swap > backvert)

  def lInvertSource[A]: One -⚬ (LPollable[A] |*| Drain[A]) =
    lInvertFollower(lInvertSignal > swap, forevert > swap)

  given drainSourceDuality[A]: Dual[Drain[A], LPollable[A]] with {
    override val rInvert: (Drain[A] |*| LPollable[A]) -⚬ One = rInvertDrain
    override val lInvert: One -⚬ (LPollable[A] |*| Drain[A]) = lInvertSource
  }

  given sourceDrainDuality[A]: Dual[LPollable[A], Drain[A]] =
    dualSymmetric(drainSourceDuality[A])
}
