package libretto.examples.interactionNets.unaryArithmetic

import libretto.scaletto.StarterKit.*
import libretto.scaletto.StarterKit.dsl.{|| as |}
import libretto.scaletto.StarterKit.scalettoLib.given
import libretto.lambda.util.SourcePos

opaque type Wire = Rec[WireF]

private type WireF[X] = Wire.ProperF[X] |+| Wire.AuxiliaryF[X]

object Wire {
  private[unaryArithmetic] type ProperF[X] = OneOf
    [ "zero"  :: One
    | "succ"  :: X
    | "plus"  :: (X |*| X)
    | "times" :: (X |*| X)
    | "dup"   :: (X |*| X)
    | "erase" :: One
    ]

  opaque type Proper = ProperF[Wire]

  object Proper {
    def unapply(using SourcePos, LambdaContext)(w: $[Wire]): Some[$[Proper]] =
      Some(w.unpackedMatchAgainst(InL.extractor))

    def zero  : One             -⚬ Proper = OneOf.make[Proper]("zero")
    def succ  : Wire            -⚬ Proper = OneOf.make[Proper]("succ")
    def plus  : (Wire |*| Wire) -⚬ Proper = OneOf.make[Proper]("plus")
    def times : (Wire |*| Wire) -⚬ Proper = OneOf.make[Proper]("times")
    def dup   : (Wire |*| Wire) -⚬ Proper = OneOf.make[Proper]("dup")
    def eraser: One             -⚬ Proper = OneOf.make[Proper]("erase")

    private val partitioning = OneOf.partition[Proper]

    object Zero:
      def unapply(using SourcePos, LambdaContext)(w: $[Proper]): Some[$[One]] =
        Some($.matchAgainst(w, partitioning["zero"])(summon[SourcePos]))

    object Succ:
      def unapply(using SourcePos, LambdaContext)(w: $[Proper]): Some[$[Wire]] =
        Some($.matchAgainst(w, partitioning["succ"])(summon[SourcePos]))

    object Plus:
      def unapply(using SourcePos, LambdaContext)(w: $[Proper]): Some[$[Wire |*| Wire]] =
        Some($.matchAgainst(w, partitioning["plus"])(summon[SourcePos]))

    object Times:
      def unapply(using SourcePos, LambdaContext)(w: $[Proper]): Some[$[Wire |*| Wire]] =
        Some($.matchAgainst(w, partitioning["times"])(summon[SourcePos]))

    object Dup:
      def unapply(using SourcePos, LambdaContext)(w: $[Proper]): Some[$[Wire |*| Wire]] =
        Some($.matchAgainst(w, partitioning["dup"])(summon[SourcePos]))

    object Eraser:
      def unapply(using SourcePos, LambdaContext)(w: $[Proper]): Some[$[One]] =
        Some($.matchAgainst(w, partitioning["erase"])(summon[SourcePos]))
  }

  private[unaryArithmetic] type AuxiliaryF[X] =
    RedirectF[X] |+| OutletF[X]

  private type RedirectF[X] = -[X]
  private type OutletF[X] = -[ProperF[X] |+| LinkId]

  opaque type LinkId = Val[AnyRef]

  opaque type Auxiliary = AuxiliaryF[Wire]

  opaque type Outlet = OutletF[Wire]

  object Auxiliary {
    def unapply(using SourcePos, LambdaContext)(w: $[Wire]): Some[$[Auxiliary]] =
      Some(w.unpackedMatchAgainst(InR.extractor))

    object Redirect:
      def unapply(using pos: SourcePos, ctx: LambdaContext)(aux: $[Auxiliary]): Some[$[-[Wire]]] =
        Some($.matchAgainst(aux, InL.extractor)(pos))

    object Outlet:
      def unapply(using pos: SourcePos, ctx: LambdaContext)(aux: $[Auxiliary]): Some[$[Outlet]] =
        Some($.matchAgainst(aux, InR.extractor)(pos))

      def feed: (Wire |*| Outlet) -⚬ One =
        λ { case w |*| out =>
          properOrLink(w) supplyTo out
        }

    def redirect: -[Wire] -⚬ Auxiliary =
      injectL

    def outlet: -[Proper |+| LinkId] -⚬ Auxiliary =
      injectR
  }

  def proper:       Proper -⚬ Wire = injectL > pack[WireF]
  def auxiliary: Auxiliary -⚬ Wire = injectR > pack[WireF]

  def newWire: One -⚬ (Wire |*| Wire) =
    forevert[Wire] > fst(Auxiliary.redirect > auxiliary)

  def read: Wire -⚬ Val[Result] = rec { read =>
    λ { w =>
      properOrLink(w) switch {
        case Left(pw) =>
          import Proper.*
          switch(pw)
            .is { case Zero(?(_))       => constantVal(Result.Zero) }
            .is { case Succ(w)          => read(w) :>> mapVal(Result.Succ(_)) }
            .is { case Plus(w1 |*| w2)  => (read(w1) ** read(w2)) :>> mapVal { case (b, out) => Result.Plus(b, out) } }
            .is { case Times(w1 |*| w2) => (read(w1) ** read(w2)) :>> mapVal { case (b, out) => Result.Times(b, out) } }
            .is { case Dup(w1 |*| w2)   => (read(w1) ** read(w2)) :>> mapVal { case (x, y) => Result.Dup(x, y) } }
            .is { case Eraser(?(_))     => constantVal(Result.Eraser) }
            .end
        case Right(lnk) =>
          lnk :>> mapVal(Result.Link(_))
      }
    }
  }

  private def properOrLink: Wire -⚬ (Proper |+| LinkId) =
    λ { w =>
      switch(w)
        .is { case Proper(p) => injectL(p) }
        .is { case Auxiliary(Redirect(redir)) =>
          val (promised |*| res) = forevert[Proper |+| LinkId]($.one)
          res alsoElim (
            auxiliary(Auxiliary.outlet(promised)) supplyTo redir
          )
        }
        .is { case Auxiliary(Outlet(outlet)) =>
          val linkId = new AnyRef
          constantVal(linkId) match {
            case +(lnk) =>
              injectR(lnk)
                .alsoElim(injectR(lnk) supplyTo outlet)
          }
        }
        .end
    }
}

import Wire.{Auxiliary, Proper}
import Wire.Auxiliary.{Outlet, Redirect}

enum Result {
  case Zero
  case Succ(n: Result)
  case Plus(b: Result, out: Result)
  case Times(b: Result, out: Result)
  case Dup(b: Result, out: Result)
  case Eraser
  case Link(id: AnyRef)
}

object Result {
  def liftInt(n: Int): Result =
    if (n > 0)
      Succ(liftInt(n-1))
    else
      Zero
}

def zero: One  -⚬ Wire = Wire.Proper.zero > Wire.proper
def succ: Wire -⚬ Wire = Wire.Proper.succ > Wire.proper

def liftInt(n: Int): One -⚬ Wire =
  if (n > 0)
    liftInt(n-1) > succ
  else
    zero

/**
  * `a + b = out`
  *
  * ```
  *         _
  *        | \
  *    b --|  \
  *        | + >-- a
  *  out --|  /
  *        |_/
  *
  * ```
  */
def plus: (Wire |*| Wire) -⚬ Wire = Wire.Proper.plus > Wire.proper

def times: (Wire |*| Wire) -⚬ Wire = Wire.Proper.times > Wire.proper

def eraser: One -⚬ Wire = Wire.Proper.eraser > Wire.proper

def dup: (Wire |*| Wire) -⚬ Wire = Wire.Proper.dup > Wire.proper

def newWire: One -⚬ (Wire |*| Wire) = Wire.newWire

def readResult: Wire -⚬ Val[Result] = Wire.read

def connect: (Wire |*| Wire) -⚬ One = rec { self =>
  λ { case (w1 |*| w2) =>
    switch(w1 |*| w2)
      .is { case Proper(p1) |*| Proper(p2)      => connectProper(self)(p1 |*| p2) }
      .is { case Auxiliary(Redirect(r1)) |*| w2 => w2 supplyTo r1 }
      .is { case w1 |*| Auxiliary(Redirect(r2)) => w1 supplyTo r2 }
      .is { case Auxiliary(Outlet(o1)) |*| w2   => Outlet.feed(w2 |*| o1) }
      .is { case w1 |*| Auxiliary(Outlet(o2))   => Outlet.feed(w1 |*| o2) }
      .end
  }
}

/** Interaction rules for all 6x6 combinations. */
private def connectProper(
  connect: (Wire |*| Wire) -⚬ One,
): (Wire.Proper |*| Wire.Proper) -⚬ One = {
  import Proper.{Zero, Succ, Plus, Times, Dup, Eraser}

  def duplicate: Wire -⚬ (Wire |*| Wire) =
    λ { w =>
      val a1 |*| a2 = constant(newWire)
      val b1 |*| b2 = constant(newWire)
      (a2 |*| b2) alsoElim connect(w |*| dup(a1 |*| b1))
    }

  def plusSucc: ((Wire |*| Wire) |*| Wire) -⚬ One =
    λ { case (b |*| out) |*| n =>
      val o1 |*| o2 = constant(newWire)
      val n1 = plus(b |*| o1)
      connect(succ(o2) |*| out) alsoElim connect(n1 |*| n)
    }

  def timesZero: (Wire |*| Wire) -⚬ One =
    λ { case b |*| out => connect(constant(zero) |*| out) alsoElim erase(b) }

  def timesSucc: ((Wire |*| Wire) |*| Wire) -⚬ One =
    λ { case (b |*| out) |*| n =>
      val b1 |*| b2 = duplicate(b)
      val out0 = plus(b2 |*| out)
      connect(times(b1 |*| out0) |*| n)
    }

  def dupZero: (Wire |*| Wire) -⚬ One =
    λ { case w1 |*| w2 => connect(constant(zero) |*| w1) alsoElim connect(constant(zero) |*| w2) }

  def dupSucc: ((Wire |*| Wire) |*| Wire) -⚬ One =
    λ { case (w1 |*| w2) |*| n =>
      val n1 |*| n2 = duplicate(n)
      connect(succ(n1) |*| w1) alsoElim connect(succ(n2) |*| w2)
    }

  def erase: Wire -⚬ One =
    λ { w => connect(w |*| constant(eraser)) }

  λ { case w1 |*| w2 =>
    switch(w2)
      .is { case Zero(?(_)) =>
        switch(w1)
          .is { case Zero(x) => x :>> undefined("0", "0") }
          .is { case Succ(x) => x :>> undefined("0", "S") }
          .is { case Plus(m1 |*| m2) => connect(m1 |*| m2) }
          .is { case Times(m1 |*| m2) => timesZero(m1 |*| m2) }
          .is { case Dup(o1 |*| o2) => dupZero(o1 |*| o2) }
          .is { case Eraser(u) => u }
          .end
      }
      .is { case Succ(n) =>
        switch(w1)
          .is { case Zero(x) => (x |*| n) :>> undefined("S", "0") }
          .is { case Succ(x) => (x |*| n) :>> undefined("S", "S") }
          .is { case Plus(m1 |*| m2) => plusSucc((m1 |*| m2) |*| n) }
          .is { case Times(m1 |*| m2) => timesSucc((m1 |*| m2) |*| n) }
          .is { case Dup(o1 |*| o2) => dupSucc((o1 |*| o2) |*| n) }
          .is { case Eraser(?(_)) => erase(n) }
          .end
      }
      .is { case Plus(n1 |*| n2) =>
        switch(w1)
          .is { case Zero(?(_)) => connect(n1 |*| n2) }
          .is { case Succ(m0) => plusSucc((n1 |*| n2) |*| m0) }
          .is { case Plus(m1 |*| m2) => ((m1 |*| m2) |*| (n1 |*| n2)) :>> undefined("+", "+") }
          .is { case Times(m1 |*| m2) => ((m1 |*| m2) |*| (n1 |*| n2)) :>> undefined("+", "*") }
          .is { case Dup(o1 |*| o2) => ((o1 |*| o2) |*| (n1 |*| n2)) :>> undefined("+", "δ") }
          .is { case Eraser(?(_)) => erase(n1) alsoElim erase(n2) }
          .end
      }
      .is { case Times(n1 |*| n2) =>
        switch(w1)
          .is { case Zero(?(_)) => timesZero(n1 |*| n2) }
          .is { case Succ(m0) => timesSucc((n1 |*| n2) |*| m0) }
          .is { case Plus(m1 |*| m2) => ((m1 |*| m2) |*| (n1 |*| n2)) :>> undefined("*", "+") }
          .is { case Times(m1 |*| m2) => ((m1 |*| m2) |*| (n1 |*| n2)) :>> undefined("*", "*") }
          .is { case Dup(m1 |*| m2) => ((m1 |*| m2) |*| (n1 |*| n2)) :>> undefined("*", "δ") }
          .is { case Eraser(?(_)) => erase(n1) alsoElim erase(n2) }
          .end
      }
      .is { case Dup(n1 |*| n2) =>
        switch(w1)
          .is { case Zero(?(_)) => dupZero(n1 |*| n2) }
          .is { case Succ(m0) => dupSucc((n1 |*| n2) |*| m0) }
          .is { case Plus(m1 |*| m2) => ((m1 |*| m2) |*| (n1 |*| n2)) :>> undefined("δ", "+") }
          .is { case Times(m1 |*| m2) => ((m1 |*| m2) |*| (n1 |*| n2)) :>> undefined("δ", "*") }
          .is { case Dup(m1 |*| m2) => connect(m1 |*| n1) alsoElim connect(m2 |*| n2) }
          .is { case Eraser(?(_)) => erase(n1) alsoElim erase(n2) }
          .end
      }
      .is { case Eraser(?(_)) =>
        switch(w1)
          .is { case Zero(u) => u }
          .is { case Succ(m0) => erase(m0) }
          .is { case Plus(m1 |*| m2) => erase(m1) alsoElim erase(m2) }
          .is { case Times(m1 |*| m2) => erase(m1) alsoElim erase(m2) }
          .is { case Dup(m1 |*| m2) => erase(m1) alsoElim erase(m2) }
          .is { case Eraser(u) => u }
          .end
      }
      .end
  }
}

private def undefined[A, B](agent1: String, agent2: String): A -⚬ B =
  crashNow(s"Undefined interaction between $agent1 and $agent2")
