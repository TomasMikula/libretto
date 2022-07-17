package libretto.mashup.rest

import libretto.mashup.{MappedValue, Runtime}
import libretto.mashup.dsl._
import libretto.mashup.rest.RelativeUrl._
import libretto.util.Async

/** Template for relative URL, parameterized by `I`. */
sealed trait RelativeUrl[I] {
  def fillParamsFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[I]): Async[String] =
    throw new NotImplementedError("fillParamsFrom")

  def matchPath(path: Path)(using rt: Runtime): Option[MappedValue[rt.type, I]]

  def map[J](f: Fun[I, J], g: Fun[J, I]): RelativeUrl[J] =
    Mapped(this, f, g)

  def map[J](f: Expr[I] => Expr[J], g: Expr[J] => Expr[I]): RelativeUrl[J] =
    this.map(fun(f), fun(g))
}

object RelativeUrl {
  case class PathAndQuery[P, Q](
    path: PathTemplate[P],
    query: Query[Q],
  ) extends RelativeUrl[(P, Q)] {
    override def matchPath(path: Path)(using rt: Runtime): Option[MappedValue[rt.type, (P, Q)]] =
      throw NotImplementedError("RelativeUrl.PathAndQuery.matchPath(Path)")
  }

  case class Mapped[I, J](
    url: RelativeUrl[I],
    f: Fun[I, J],
    g: Fun[J, I],
  ) extends RelativeUrl[J] {

    override def matchPath(path: Path)(using rt: Runtime): Option[MappedValue[rt.type, J]] =
      throw NotImplementedError("RelativeUrl.Mapped.matchPath(Path)")
  }

  case class PathOnly[I](path: PathTemplate[I]) extends RelativeUrl[I] {
    override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, I]] =
      path.matchPath(p)

    def /(segment: String): PathOnly[I] =
      PathOnly(path / segment)

    def /[J](param: PathTemplate.Param[J])(using I =:= EmptyResource): PathOnly[J] =
      PathOnly(path / param)
  }

  sealed trait PathTemplate[I] {
    def /(segment: String): PathTemplate[I]
    def /[J](param: PathTemplate.Param[J])(using I =:= EmptyResource): PathTemplate[J]

    def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, I]]
  }

  object PathTemplate {
    case object Empty extends PathTemplate[EmptyResource] {
      override def /(segment: String): PathTemplate[EmptyResource] =
        Constant(segment)

      override def /[J](param: PathTemplate.Param[J])(using EmptyResource =:= EmptyResource): PathTemplate[J] =
        param

      override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, EmptyResource]] =
        p match {
          case Path.Empty => Some(MappedValue.pure(rt.Value.unit))
          case _          => None
        }
    }

    sealed trait NonEmpty[I] extends PathTemplate[I] {
      override def /(segment: String): PathTemplate[I] =
        throw new NotImplementedError("NonEmpty./(segment)")
      override def /[J](param: PathTemplate.Param[J])(using I =:= EmptyResource): PathTemplate[J] =
        throw new NotImplementedError("NonEmpty./(param)")
    }

    case class Constant(segment: String) extends PathTemplate.NonEmpty[EmptyResource] {
      override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, EmptyResource]] =
        p match {
          case Path.NonEmpty(Nil, lastSegment) =>
            lastSegment match {
              case Path.LastSegment.NonEmpty(seg) if seg == Path.segment(segment) =>
                Some(MappedValue.pure(rt.Value.unit))
              case Path.LastSegment.SlashTerminated(seg) if seg == Path.segment(segment) =>
                Some(MappedValue.pure(rt.Value.unit))
              case _ =>
                None
            }
          case _ =>
            None
        }
    }

    case class Param[I](codec: Codec[I]) extends PathTemplate.NonEmpty[I] {
      override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, I]] =
        p match {
          case Path.NonEmpty(Nil, lastSegment) =>
            val s = lastSegment.segment.asString
            codec.decode(s) match {
              case Right(value) => Some(MappedValue.pure(value))
              case Left(_)      => None
            }
          case _ =>
            None
        }
    }

    case class Composed[I, J](p: PathTemplate.NonEmpty[I], q: PathTemplate.NonEmpty[J]) extends PathTemplate.NonEmpty[(I, J)] {
      override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, (I, J)]] =
        throw new NotImplementedError("Composed.matchPath(Path)")
    }
    case class Mapped[I, J](p: PathTemplate[I], f: Fun[I, J], g: Fun[J, I]) extends PathTemplate[J] {
      override def /(segment: String): PathTemplate[J] =
        throw new NotImplementedError("Mapped./(segment)")

      override def /[K](param: PathTemplate.Param[K])(using J =:= EmptyResource): PathTemplate[K] =
        throw new NotImplementedError("Mapped./(param)")

      override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, J]] =
        throw new NotImplementedError("Mapped.matchPath(Path)")
    }
  }

  sealed trait Query[I]

  def empty: PathOnly[EmptyResource] =
    PathOnly(PathTemplate.Empty)

  def path(segment: String): PathOnly[EmptyResource] =
    PathOnly(PathTemplate.Constant(segment))

  def path[I](using codec: Codec[I]): PathOnly[I] =
    PathOnly(param[I])

  def param[I](using codec: Codec[I]): PathTemplate.Param[I] =
    PathTemplate.Param(codec)
}
