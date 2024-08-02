package libretto.stream.invert

import libretto.invert.InvertDSL
import libretto.puro.PuroLib
import libretto.stream.puro.PuroStreams
import libretto.util.∀

object InvertStreams {
  def apply(
    dsl: InvertDSL,
    lib: PuroLib[dsl.type],
  )
  : InvertStreams[dsl.type, lib.type] =
    new InvertStreams(dsl, lib)
}

class InvertStreams[DSL <: InvertDSL, Lib <: PuroLib[DSL]](
  override val dsl: DSL,
  override val lib: Lib & PuroLib[dsl.type],
) extends PuroStreams[DSL, Lib](dsl, lib) {
  import dsl.*
  import dsl.$.*
  import lib.*

  opaque type Drain[A] = StreamT[Need, -[A]]
  opaque type Sink[A]  = SourceT[Need, -[A]]

  object Drain {
    type Pulling[A] = Need |&| (-[A] |*| Drain[A])

    def close[A]: Drain[A] -⚬ Need =
      StreamT.switch(id, chooseL)

    def closed[A]: Need -⚬ Drain[A] =
      StreamT.closed[Need, -[A]]

    def pulling[A]: Pulling[A] -⚬ Drain[A] =
      StreamT.next[Need, -[A]]

    def switch[A, R](
      onClose: Need -⚬ R,
      onPull: Pulling[A] -⚬ R,
    ): Drain[A] -⚬ R =
      StreamT.switch(onClose, onPull)

    def toEither[A]: Drain[A] -⚬ (Need |+| Pulling[A]) =
      StreamT.toEither

    def fromEither[A]: (Need |+| Pulling[A]) -⚬ Drain[A] =
      StreamT.fromEither

    def onCloseAwait[A]: (Done |*| Drain[A]) -⚬ Drain[A] = rec { self =>
      λ { case (d |*| drain) =>
        toEither(drain) either {
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

  def rInvertDrain[A]: (Drain[A] |*| Source[A]) -⚬ One =
    rInvertStreamT[Need, Done, -[A], A](swap > rInvertSignal, backvert)

  def lInvertSource[A]: One -⚬ (Source[A] |*| Drain[A]) =
    lInvertSourceT(lInvertSignal > swap, forevert)

  def rInvertStream[A]: (Stream[A] |*| Sink[A]) -⚬ One =
    rInvertStreamT[Done, Need, A, -[A]](rInvertSignal, swap > backvert)

  def lInvertSink[A]: One -⚬ (Sink[A] |*| Stream[A]) =
    lInvertSourceT[Need, Done, -[A], A](lInvertSignal, forevert > swap)

  given drainSourceDuality[A]: Dual[Drain[A], Source[A]] with {
    override val rInvert: (Drain[A] |*| Source[A]) -⚬ One = rInvertDrain
    override val lInvert: One -⚬ (Source[A] |*| Drain[A]) = lInvertSource
  }

  given sourceDrainDuality[A]: Dual[Source[A], Drain[A]] =
    dualSymmetric(drainSourceDuality[A])

  given streamSinkDuality[A]: Dual[Stream[A], Sink[A]] with {
    override val rInvert = rInvertStream
    override val lInvert = lInvertSink
  }

  given sinkStreamDuality[A]: Dual[Sink[A], Stream[A]] =
    dualSymmetric(streamSinkDuality[A])
}
