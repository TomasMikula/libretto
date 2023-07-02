package libretto.mashup.rest

import libretto.mashup.{MappedValue, Runtime}
import libretto.mashup.dsl.*
import libretto.util.Async
import scala.util.{Failure, Success, Try}

sealed trait PathTemplate[I] {
  def </>[J](that: PathTemplate.Segment[J]): PathTemplate[I ** J]

  def fillParamsFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[I]): Async[Try[String]]

  def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, I]]

  def /(segment: String): PathTemplate[I] =
    (this </> PathTemplate.Constant(segment)).adapt(
      fun { case (i ** e) => i.alsoElim(e) },
      fun { i => i ** Expr.unit },
    )

  def /[J](param: PathTemplate.Param[J])(using ev: I =:= EmptyResource): PathTemplate[J] =
    (this </> param).adapt(
      fun { case (i ** j) => j.alsoElim(ev.substituteCo(i)) },
      fun { j => ev.substituteContra(Expr.unit) ** j },
    )

  def adapt[J](f: Fun[I, J], g: Fun[J, I]): PathTemplate[J] =
    PathTemplate.Adapted(this, f, g)
}

object PathTemplate {
  case object Empty extends PathTemplate[EmptyResource] {
    override def </>[J](that: PathTemplate.Segment[J]): PathTemplate[EmptyResource ** J] =
      SingleSegment(that).adapt(
        fun { j => Expr.unit ** j },
        fun { case (u ** j) => j.alsoElim(u) },
      )

    override def fillParamsFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[EmptyResource]): Async[Try[String]] = {
      exn.OutPort.emptyResourceIgnore(port)
      Async.now(Success(""))
    }

    override def /(segment: String): PathTemplate[EmptyResource] =
      SingleSegment(Constant(segment))

    override def /[J](param: PathTemplate.Param[J])(using EmptyResource =:= EmptyResource): PathTemplate[J] =
      SingleSegment(param)

    override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, EmptyResource]] =
      p match {
        case Path.Empty => Some(MappedValue.pure(rt.Value.unit))
        case _          => None
      }
  }

  sealed trait NonEmpty[I] extends PathTemplate[I] {
    override def </>[J](that: PathTemplate.Segment[J]): PathTemplate[I ** J] =
      PathTemplate.Snoc(this, that)

    def matchSegments(segments: List[Path.Segment])(using rt: Runtime): Option[rt.Value[I]] = {
      val e = new NotImplementedError(s"${this}.matchSegments(${segments})")
      e.printStackTrace(Console.err)
      throw e
    }
  }

  case class SingleSegment[I](segment: Segment[I]) extends PathTemplate.NonEmpty[I] {
    override def fillParamsFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[I]): Async[Try[String]] =
      segment.readFrom(port)

    override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, I]] =
      p match {
        case Path.NonEmpty(Nil, lastSegment) =>
          // TODO: consider lastSegment's trailing slash
          (segment matches lastSegment.segment).map(MappedValue.pure(_))
        case _ =>
          None
      }

    override def matchSegments(segments: List[Path.Segment])(using rt: Runtime): Option[rt.Value[I]] =
      segments match {
        case seg :: Nil => segment matches seg
        case _          => None
      }
  }

  case class Snoc[I, J](
    init: PathTemplate.NonEmpty[I],
    last: Segment[J],
  ) extends PathTemplate.NonEmpty[I ** J] {
    override def fillParamsFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[I ** J]): Async[Try[String]] = {
      val (pi, pj) = exn.OutPort.split(port)
      for {
        s <- init.fillParamsFrom(pi)
        t <- last.readFrom(pj)
      } yield {
        for {
          s <- s
          t <- t
        } yield s"$s/$t"
      }
    }

    override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, I ** J]] =
      p match {
        case Path.NonEmpty(segments, lastSegment) =>
          for {
            initMatch <- init.matchSegments(segments)
            lastMatch <- last.matches(lastSegment.segment) // TODO: consider lastSegment's trailing slash
          } yield MappedValue.pure(initMatch ** lastMatch)
        case Path.Empty =>
          None
      }
  }

  case class Adapted[I, J](
    base: PathTemplate[I],
    f: Fun[I, J],
    g: Fun[J, I],
  ) extends PathTemplate[J] {
    override def fillParamsFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[J]): Async[Try[String]] = {
      val pi = exn.OutPort.map(port)(g)
      base.fillParamsFrom(pi)
    }

    override def </>[K](that: Segment[K]): PathTemplate[J ** K] =
      Adapted(
        base </> that,
        fun { case (i ** k) => f(i) ** k },
        fun { case (j ** k) => g(j) ** k },
      )

    override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, J]] =
      base.matchPath(p).map(_.map(f))
  }

  sealed trait Segment[I] {
    def readFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[I]): Async[Try[String]]
    def matches(segment: Path.Segment)(using rt: Runtime): Option[rt.Value[I]]
  }

  case class Constant(segment: String) extends PathTemplate.Segment[EmptyResource] {
    override def readFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[EmptyResource]): Async[Try[String]] = {
      val () = exn.OutPort.emptyResourceIgnore(port)
      Async.now(Success(segment))
    }

    override def matches(seg: Path.Segment)(using rt: Runtime): Option[rt.Value[EmptyResource]] =
      if (seg == Path.segment(segment))
        Some(rt.Value.unit)
      else
        None
  }

  case class Param[I](codec: StringCodec[I]) extends PathTemplate.Segment[I] {
    override def readFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[I]): Async[Try[String]] = {
      codec.encodeFrom(port)
    }

    override def matches(seg: Path.Segment)(using rt: Runtime): Option[rt.Value[I]] =
      codec.decode(seg.asString) match {
        case Right(value) => Some(value)
        case Left(_)      => None
      }
  }
}
