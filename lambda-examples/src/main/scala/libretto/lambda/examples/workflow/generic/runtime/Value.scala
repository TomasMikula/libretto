package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.{DistributionNAry, EnumModule, Member, Projection, UnhandledCase, Unzippable, Zippable}
import libretto.lambda.examples.workflow.generic.lang.{**, ++, ||, ::, Enum, PortName, Reading, Str, given}
import libretto.lambda.util.Exists
import libretto.lambda.util.unapply.Unapply

enum Value[F[_], A]:
  case One[F[_]]() extends Value[F, Unit]

  case StringValue[F[_]](value: String) extends Value[F, Str]

  case Pair[F[_], A1, A2](
    a1: Value[F, A1],
    a2: Value[F, A2],
  ) extends Value[F, A1 ** A2]

  case Inject[F[_], Label, A, Cases](
    i: Member[||, ::, Label, A, Cases],
    a: Value[F, A],
  ) extends Value[F, Enum[Cases]]

  case PortNameValue[F[_], A](w: WorkflowRef[?], pa: PortId[A]) extends Value[F, PortName[A]]
  case ReadingInput[F[_], A](pa: PortId[A]) extends Value[F, Reading[A]]

  /** Extension point for domain-specific values. */
  case Ext(value: F[A])

  def as[B](using ev: A =:= B): Value[F, B] =
    ev.substituteCo(this)

  def **[B](that: Value[F, B]): Value[F, A ** B] =
    Pair(this, that)

  def discard[B](p: Projection[**, A, B])(using Unzippable[**, F]): Value[F, B] =
    p match
      case Projection.Id()                => this
      case p: Projection.Proper[pr, a, b] => discardProper(p)

  def discardProper[B](p: Projection.Proper[**, A, B])(using Unzippable[**, F]): Value[F, B] =
    p.startsFromPair match
      case Exists.Some(Exists.Some(ev)) =>
        Value.discardProper(this.as(using ev), p.from(using ev.flip))

object Value:
  def unit[F[_]]: Value[F, Unit] =
    Value.One()

  def string[F[_]](s: String): Value[F, Str] =
    Value.StringValue(s)

  def left[F[_], A, B](value: Value[F, A]): Value[F, A ++ B] =
    Value.ofEnum[F, "Left", A, "Left" :: A || "Right" :: B](summon, value)

  def right[F[_], A, B](value: Value[F, B]): Value[F, A ++ B] =
    Value.ofEnum[F, "Right", B, "Left" :: A || "Right" :: B](summon, value)

  def ofEnum[F[_], Label, A, Cases](
    i: Member[||, ::, Label, A, Cases],
    a: Value[F, A],
  ): Value[F, Enum[Cases]] =
    Value.Inject(i, a)

  def ofEnum[T](using u: Unapply[T, Enum]): ValueOfEnumBuilder[u.A] =
    ValueOfEnumBuilder[u.A]

  class ValueOfEnumBuilder[Cases]:
    def apply[Lbl](using m: Member[||, ::, Lbl, ?, Cases]): ValueOfEnumCaseBuilder[Lbl, m.Type, Cases] =
      ValueOfEnumCaseBuilder[Lbl, m.Type, Cases](m)

  class ValueOfEnumCaseBuilder[Lbl, A, Cases](m: Member[||, ::, Lbl, A, Cases]):
    def apply[F[_]](a: Value[F, A]): Value[F, Enum[Cases]] =
      Value.ofEnum(m, a)

  def portName[F[_], A](w: WorkflowRef[?], promiseId: PortId[A]): Value[F, PortName[A]] =
    PortNameValue(w, promiseId)

  def reading[F[_], A](pa: PortId[A]): Value[F, Reading[A]] =
    ReadingInput(pa)

  trait Compliant[F[_]] extends Unzippable[**, F]:
    def extractString(value: F[Str]): String
    def toEither[A, B](value: F[A ++ B]): Either[F[A], F[B]]
    def extractPortId[A](value: F[Reading[A]]): PortId[A]
    def revealCase[Cases](value: F[Enum[Cases]]): Exists[[Lbl] =>> Exists[[A] =>> Value.Inject[F, Lbl, A, Cases]]]

  def unpair[F[_], A, B](value: Value[F, A ** B])(using F: Unzippable[**, F]): (Value[F, A], Value[F, B]) =
    value match
      case Pair(a, b) =>
        (a, b)
      case Ext(value) =>
        val (a, b) = F.unzip(value)
        (Ext(a), Ext(b))

  def toEither[F[_], A, B](value: Value[F, A ++ B])(using F: Compliant[F]): Either[Value[F, A], Value[F, B]] =
    value match
      case Value.Inject(mem, value) =>
        toEither(mem, value)
      case Ext(value) =>
        F.toEither(value).left.map(Ext(_)).map(Ext(_))

  private def toEither[F[_], Lbl, X, A, B](
    mem: Member[||, ::, Lbl, X, "Left" :: A || "Right" :: B],
    value: Value[F, X],
  ): Either[Value[F, A], Value[F, B]] = {
    import Member.{InInit, InLast, Single}

    mem match
      case InLast(_) =>
        summon[X =:= B]
        Right(value)
      case InInit(Single(_)) =>
        summon[X =:= A]
        Left(value)
  }

  def revealCase[F[_], Cases](
    v: Value[F, Enum[Cases]]
  )(using
    F: Compliant[F],
  ): Exists[[Lbl] =>> Exists[[A] =>> Value.Inject[F, Lbl, A, Cases]]] =
    v match
      case Inject(i, a) =>
        Exists(Exists(Inject(i, a)))
      case Ext(value) =>
        F.revealCase(value)
      case One() | Pair(_, _) | PortNameValue(_, _) | ReadingInput(_) =>
        throw AssertionError(s"Impossible for $v to represent an Enum value")

  def distLRNAry[F[_], X, Cases, XCases](
    x: Value[F, X],
    enm: Value[F, Enum[Cases]],
    d: DistributionNAry.DistLR[**, ||, ::, X, Cases] { type Out = XCases },
  )(using
    F: Compliant[F],
  ): Value[F, Enum[XCases]] =
    revealCase(enm) match
      case Exists.Some(Exists.Some(Inject(i, a))) =>
        Inject(d.distributeOver(i), x ** a)

  def extractString[F[_]](value: Value[F, Str])(using F: Compliant[F]): String =
    value match
      case StringValue(s) => s
      case Ext(value) => F.extractString(value)

  def extractPortId[F[_], A](value: Value[F, Reading[A]])(using F: Compliant[F]): PortId[A] =
    value match
      case ReadingInput(pa) => pa
      case Ext(value) => F.extractPortId(value)

  given zippableValue[F[_]]: Zippable[**, Value[F, _]] with
    override def zip[A, B](fa: Value[F, A], fb: Value[F, B]): Value[F, A ** B] =
      Pair(fa, fb)

  given unzippableValue[F[_]](using Unzippable[**, F]): Unzippable[**, Value[F, _]] with
    override def unzip[A, B](fab: Value[F, A ** B]): (Value[F, A], Value[F, B]) =
      Value.unpair(fab)

  private[Value] def discardProper[F[_], A1, A2, B](
    value: Value[F, A1 ** A2],
    p: Projection.Proper[**, A1 ** A2, B],
  )(using
    Unzippable[**, F],
  ): Value[F, B] =
    val (a1, a2) = unpair(value)
    p match
      case Projection.DiscardFst(p2) =>
        a2.discard(p2)
      case Projection.DiscardSnd(p1) =>
        a1.discard(p1)
      case Projection.Fst(p1) =>
        a1.discardProper(p1) ** a2
      case Projection.Snd(p2) =>
        a1 ** a2.discardProper(p2)
      case Projection.Both(p1, p2) =>
        a1.discardProper(p1) ** a2.discardProper(p2)
