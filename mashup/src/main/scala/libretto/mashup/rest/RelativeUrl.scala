package libretto.mashup.rest

import libretto.mashup.{MappedValue, Runtime}
import libretto.mashup.dsl.*
import libretto.mashup.rest.RelativeUrl.*
import libretto.util.Async
import scala.util.Try

/** Template for relative URL, parameterized by `I`. */
sealed trait RelativeUrl[I] {
  def fillParamsFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[I]): Async[Try[String]]

  def matchPath(path: Path)(using rt: Runtime): Option[MappedValue[rt.type, I]]

  def map[J](f: Fun[I, J], g: Fun[J, I]): RelativeUrl[J] =
    Mapped(this, f, g)

  infix def map[J](f: Expr[I] => Expr[J], g: Expr[J] => Expr[I]): RelativeUrl[J] =
    this.map(fun(f), fun(g))
}

object RelativeUrl {
  case class PathAndQuery[P, Q](
    path: PathTemplate[P],
    query: Query[Q],
  ) extends RelativeUrl[(P, Q)] {
    override def fillParamsFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[(P, Q)]): Async[Try[String]] = {
      val e = NotImplementedError("PathAndQueyr#fillParamsFrom")
      e.printStackTrace(Console.err)
      throw e
    }

    override def matchPath(path: Path)(using rt: Runtime): Option[MappedValue[rt.type, (P, Q)]] = {
      val e = NotImplementedError("RelativeUrl.PathAndQuery#matchPath(Path)")
      e.printStackTrace(Console.err)
      throw e
    }
  }

  case class Mapped[I, J](
    base: RelativeUrl[I],
    f: Fun[I, J],
    g: Fun[J, I],
  ) extends RelativeUrl[J] {
    override def fillParamsFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[J]): Async[Try[String]] = {
      val pi = exn.OutPort.map(port)(g)
      base.fillParamsFrom(pi)
    }

    override def matchPath(path: Path)(using rt: Runtime): Option[MappedValue[rt.type, J]] =
      base.matchPath(path).map(_.map(f))
  }

  case class PathOnly[I](path: PathTemplate[I]) extends RelativeUrl[I] {
    override def fillParamsFrom(using rt: Runtime, exn: rt.Execution)(port: exn.OutPort[I]): Async[Try[String]] =
      path.fillParamsFrom(port)

    override def matchPath(p: Path)(using rt: Runtime): Option[MappedValue[rt.type, I]] =
      path.matchPath(p)

    def /(segment: String): PathOnly[I] =
      PathOnly(path / segment)

    def /[J](param: PathTemplate.Param[J])(using I =:= EmptyResource): PathOnly[J] =
      PathOnly(path / param)
  }

  sealed trait Query[I]

  def empty: PathOnly[EmptyResource] =
    PathOnly(PathTemplate.Empty)

  def path(segment: String): PathOnly[EmptyResource] =
    PathOnly(PathTemplate.SingleSegment(PathTemplate.Constant(segment)))

  def path[I](using codec: StringCodec[I]): PathOnly[I] =
    PathOnly(PathTemplate.SingleSegment(param[I]))

  def param[I](using codec: StringCodec[I]): PathTemplate.Param[I] =
    PathTemplate.Param(codec)
}
