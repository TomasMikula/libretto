package libretto.examples.interactionNets.unaryArithmetic

import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.scalettoLib.given
import libretto.lambda.util.SourcePos

opaque type Wire = Rec[WireF]

private type WireF[X] = Wire.ProperF[X] |+| Wire.AuxiliaryF[X]

object Wire {
  private[unaryArithmetic] type ProperF[X] =
    /* zero  */ One
    /* succ  */ |+| X
    /* plus  */ |+| (X |*| X)
    /* times */ |+| (X |*| X)
    /* dup   */ |+| (X |*| X)
    /* erase */ |+| One

  opaque type Proper = ProperF[Wire]

  object Proper {
    def zero  : One             -⚬ Proper = injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectL
    def succ  : Wire            -⚬ Proper = injectL ∘ injectL ∘ injectL ∘ injectL ∘ injectR
    def plus  : (Wire |*| Wire) -⚬ Proper = injectL ∘ injectL ∘ injectL ∘ injectR
    def times : (Wire |*| Wire) -⚬ Proper = injectL ∘ injectL ∘ injectR
    def dup   : (Wire |*| Wire) -⚬ Proper = injectL ∘ injectR
    def eraser: One             -⚬ Proper = injectR

    def switchWith[A, R](
      caseZero: A -⚬ R,
      caseSucc: (A |*| Wire) -⚬ R,
      casePlus: (A |*| (Wire |*| Wire)) -⚬ R,
      caseTimes: (A |*| (Wire |*| Wire)) -⚬ R,
      caseDup: (A |*| (Wire |*| Wire)) -⚬ R,
      caseEraser: A -⚬ R,
    ): (A |*| Proper) -⚬ R =
      λ { case a |*| p =>
        p switch {
          case Right(?(eraser)) =>
            caseEraser(a)
          case Left(p) =>
            p switch {
              case Right(dup) =>
                caseDup(a |*| dup)
              case Left(p) =>
                p switch {
                  case Right(times) =>
                    caseTimes(a |*| times)
                  case Left(p) =>
                    p switch {
                      case Right(plus) =>
                        casePlus(a |*| plus)
                      case Left(p) =>
                        p switch {
                          case Right(succ) =>
                            caseSucc(a |*| succ)
                          case Left(?(zero)) =>
                            caseZero(a)
                        }
                    }
                }
            }
        }
      }

    def switchWithR[B, T](
      caseZero: B -⚬ T,
      caseSucc: (Wire |*| B) -⚬ T,
      casePlus: ((Wire |*| Wire) |*| B) -⚬ T,
      caseTimes: ((Wire |*| Wire) |*| B) -⚬ T,
      caseDup: ((Wire |*| Wire) |*| B) -⚬ T,
      caseEraser: B -⚬ T,
    ): (Proper |*| B) -⚬ T =
      swap > switchWith(
        caseZero,
        swap > caseSucc,
        swap > casePlus,
        swap > caseTimes,
        swap > caseDup,
        caseEraser,
      )

    def switch[R](
      caseZero: One -⚬ R,
      caseSucc: Wire -⚬ R,
      casePlus: (Wire |*| Wire) -⚬ R,
      caseTimes: (Wire |*| Wire) -⚬ R,
      caseDup: (Wire |*| Wire) -⚬ R,
      caseEraser: One -⚬ R,
    ): Proper -⚬ R =
      introFst[Proper] > switchWith(
        caseZero,
        elimFst > caseSucc,
        elimFst > casePlus,
        elimFst > caseTimes,
        elimFst > caseDup,
        caseEraser,
      )
  }

  private[unaryArithmetic] type AuxiliaryF[X] =
    RedirectF[X] |+| OutletF[X]

  private type RedirectF[X] = -[X]
  private type OutletF[X] = -[ProperF[X] |+| LinkId]

  opaque type LinkId = Val[AnyRef]

  opaque type Auxiliary = AuxiliaryF[Wire]

  opaque type Outlet = OutletF[Wire]

  object Outlet {
    def feedProper: (Proper |*| Outlet) -⚬ One =
      λ { case p |*| out =>
        injectL(p) supplyTo out
      }

    def feed: (Wire |*| Outlet) -⚬ One =
      λ { case w |*| out =>
        properOrLink(w) supplyTo out
      }
  }

  object Auxiliary {
    def redirect: -[Wire] -⚬ Auxiliary =
      injectL

    def outlet: -[Proper |+| LinkId] -⚬ Auxiliary =
      injectR

    def switch[R](w: $[Auxiliary])(f: LambdaContext ?=> Either[$[-[Wire]], $[Outlet]] => $[R])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[R] =
      $.switchEither(w, f)(pos)
  }

  def proper:       Proper -⚬ Wire = injectL > pack[WireF]
  def auxiliary: Auxiliary -⚬ Wire = injectR > pack[WireF]

  def newWire: One -⚬ (Wire |*| Wire) =
    forevert[Wire] > fst(Auxiliary.redirect > auxiliary)

  def switch[R](w: $[Wire])(f: LambdaContext ?=> Either[$[Proper], $[Auxiliary]] => $[R])(using
    pos: SourcePos,
    ctx: LambdaContext,
  ): $[R] =
    $.switchEither(w :>> unpack[WireF], f)(pos)

  def read: Wire -⚬ Val[Result] = rec { read =>
    λ { w =>
      properOrLink(w) switch {
        case Left(pw) =>
          pw :>> Proper.switch(
            caseZero = const(Result.Zero),
            caseSucc = read > mapVal(Result.Succ(_)),
            casePlus = par(read, read) > unliftPair > mapVal { case (b, out) => Result.Plus(b, out) },
            caseTimes = par(read, read) > unliftPair > mapVal { case (b, out) => Result.Times(b, out) },
            caseDup = par(read, read) > unliftPair > mapVal { case (x, y) => Result.Dup(x, y) },
            caseEraser = const(Result.Eraser),
          )
        case Right(lnk) =>
          lnk :>> mapVal(Result.Link(_))
      }
    }
  }

  private def properOrLink: Wire -⚬ (Proper |+| LinkId) =
    λ { w =>
      Wire.switch(w) {
        case Left(p) =>
          injectL(p)
        case Right(aux) =>
          Auxiliary.switch(aux) {
            case Left(redir) =>
              val (promised |*| res) = forevert[Proper |+| LinkId]($.one)
              res alsoElim (
                auxiliary(Auxiliary.outlet(promised)) supplyTo redir
              )
            case Right(outlet) =>
              val linkId = new AnyRef
              constantVal(linkId) match {
                case +(lnk) =>
                  injectR(lnk)
                    .alsoElim(injectR(lnk) supplyTo outlet)
              }
          }
      }
    }
}

import Wire.Outlet

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
    Wire.switch(w1) {
      case Left(proper1) =>
        Wire.switch(w2) {
          case Left(proper2) => connectProper(self)(proper1 |*| proper2)
          case Right(aux2) =>
            Wire.Auxiliary.switch(aux2) {
              case Left(redirect) => Wire.proper(proper1) supplyTo redirect
              case Right(outlet)  => Outlet.feedProper(proper1 |*| outlet)
            }
        }
      case Right(aux1) =>
        Wire.Auxiliary.switch(aux1) {
          case Left(redirect) => w2 supplyTo redirect
          case Right(outlet)  => Outlet.feed(w2 |*| outlet)
        }
    }
  }
}

/** Interaction rules for all 6x6 combinations. */
private def connectProper(
  connect: (Wire |*| Wire) -⚬ One,
): (Wire.Proper |*| Wire.Proper) -⚬ One = {
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

  Wire.Proper.switchWith(
    caseZero =
      Wire.Proper.switch(
        caseZero = undefined("0", "0"),
        caseSucc = undefined("0", "S"),
        casePlus = connect,
        caseTimes = timesZero,
        caseDup = dupZero,
        caseEraser = id[One],
      ),
    caseSucc =
      Wire.Proper.switchWithR(
        caseZero = undefined("S", "0"),
        caseSucc = undefined("S", "S"),
        casePlus = plusSucc,
        caseTimes = timesSucc,
        caseDup = dupSucc,
        caseEraser = erase,
      ),
    casePlus =
      Wire.Proper.switchWithR(
        caseZero = connect,
        caseSucc = swap > plusSucc,
        casePlus = undefined("+", "+"),
        caseTimes = undefined("+", "*"),
        caseDup = undefined("+", "δ"),
        caseEraser = parToOne(erase, erase),
      ),
    caseTimes =
      Wire.Proper.switchWithR(
        caseZero = swap > timesZero,
        caseSucc = swap > timesSucc,
        casePlus = undefined("*", "+"),
        caseTimes = undefined("*", "*"),
        caseDup = undefined("*", "δ"),
        caseEraser = parToOne(erase, erase),
      ),
    caseDup =
      Wire.Proper.switchWithR(
        caseZero = dupZero,
        caseSucc = swap > dupSucc,
        casePlus = undefined("δ", "+"),
        caseTimes = undefined("δ", "*"),
        caseDup = λ { case (a1 |*| a2) |*| (b1 |*| b2) => connect(a1 |*| b1) alsoElim connect(a2 |*| b2) },
        caseEraser = parToOne(erase, erase),
      ),
    caseEraser =
      Wire.Proper.switch(
        caseZero = id[One],
        caseSucc = erase,
        casePlus = parToOne(erase, erase),
        caseTimes = parToOne(erase, erase),
        caseDup = parToOne(erase, erase),
        caseEraser = id[One],
      ),
  )
}

private def undefined[A, B](agent1: String, agent2: String): A -⚬ B =
  crashNow(s"Undefined interaction between $agent1 and $agent2")
