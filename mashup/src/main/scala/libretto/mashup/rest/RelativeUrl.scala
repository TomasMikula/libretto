package libretto.mashup.rest

import libretto.mashup.dsl._
import libretto.mashup.rest.RelativeUrl._

/** Template for relative URL, parameterized by `I`. */
sealed trait RelativeUrl[I]

object RelativeUrl {
  case class PathAndQuery[P, Q](
    path: Path[P],
    query: Query[Q],
  ) extends RelativeUrl[(P, Q)]

  case class Mapped[I, J](
    url: RelativeUrl[I],
    f: Fun[I, J],
    g: Fun[J, I],
  ) extends RelativeUrl[J]

  sealed trait Path[I] extends RelativeUrl[I] {
    def /(segment: String): Path[I]
    def /[J](param: Path.Param[J])(using I =:= Unit): Path[J]
  }

  object Path {
    case object Empty extends Path[Unit] {
      override def /(segment: String): Path[Unit] =
        Constant(segment)
      override def /[J](param: Path.Param[J])(using Unit =:= Unit): Path[J] =
        param
    }
    sealed trait NonEmpty[I] extends Path[I] {
      override def /(segment: String): Path[I] =
        ???
      override def /[J](param: Path.Param[J])(using I =:= Unit): Path[J] =
        ???
    }
    case class Constant(segment: String) extends Path.NonEmpty[Unit]
    case class Param[I](codec: UrlCodec[I]) extends Path.NonEmpty[I]
    case class Composed[I, J](p: Path.NonEmpty[I], q: Path.NonEmpty[J]) extends Path.NonEmpty[(I, J)]
    case class Mapped[I, J](p: Path[I], f: Fun[I, J], g: Fun[J, I]) extends Path[J] {
      override def /(segment: String): Path[J] =
        ???
      override def /[K](param: Path.Param[K])(using J =:= Unit): Path[K] =
        ???
    }
  }

  sealed trait Query[I]

  def empty: Path[Unit] =
    Path.Empty

  def path(segment: String): Path[Unit] =
    Path.Constant(segment)

  def path[I](using codec: UrlCodec[I]): Path.Param[I] =
    Path.Param(codec)
}
