package libretto.typology.toylang.types

import libretto.typology.kinds._


opaque type TypeTag[A <: AnyKind] = TypeFun[Nothing, ?, ?]

object TypeTag {
  def apply[A <: AnyKind](using a: TypeTag[A]): TypeTag[A] =
    a

  given unit: TypeTag[Unit] = TypeFun.unit
  given int: TypeTag[Int] = TypeFun.int
  given string: TypeTag[String] = TypeFun.string

  given pair: TypeTag[Tuple2] =
    TypeFun.pair

  given pair[A, B](using a: TypeTag[A], b: TypeTag[B]): TypeTag[(A, B)] =
    TypeFun.pair(
      (a: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ○, ●]],
      (b: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ○, ●]],
    )

  given pair1[A](using a: TypeTag[A]): TypeTag[(A, *)] =
    TypeFun.pair1(
      (a: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ○, ●]]
    )

  given sum: TypeTag[Either] =
    TypeFun.sum

  given sum1[A](using a: TypeTag[A]): TypeTag[Either[A, *]] =
    TypeFun.sum1(
      (a: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ○, ●]]
    )

  given fix[F[_]](using f: TypeTag[F]): TypeTag[Fix[F]] =
    TypeFun.fix(
      (f: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ●, ●]]
    )

  given pfix[F[_, _]](using f: TypeTag[F]): TypeTag[[x] =>> Fix[F[x, *]]] =
    TypeFun.pfix(
      (f: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ● × ●, ●]]
    )

  def compose[F[_], G[_]](f: TypeTag[F], g: TypeTag[G]): TypeTag[[x] =>> F[G[x]]] = {
    val f1 = (f: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ●, ●]]
    val g1 = (g: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ●, ●]]
    f1 ∘ g1
  }

  def compose2[F[_], G[_, _]](f: TypeTag[F], g: TypeTag[G]): TypeTag[[x, y] =>> F[G[x, y]]] = {
    val f1 = (f: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ●, ●]]
    val g1 = (g: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ● × ●, ●]]
    f1 ∘ g1
  }

  def composeSnd[F[_, _], H[_]](f: TypeTag[F], h: TypeTag[H]): TypeTag[[x, y] =>> F[x, H[y]]] = {
    val f1 = (f: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ● × ●, ●]]
    val h1 = (h: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ●, ●]]
    TypeFun.composeSnd(f1, h1)
  }

  def app[F[_], A](f: TypeTag[F], a: TypeTag[A]): TypeTag[F[A]] = {
    val f1 = (f: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ●, ●]]
    val a1 = (a: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ○, ●]]
    TypeFun.fromExpr(f1(toType(a1)))
  }

  def appFst[F[_, _], A](f: TypeTag[F], a: TypeTag[A]): TypeTag[F[A, *]] = {
    val f1 = (f: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ● × ●, ●]]
    val a1 = (a: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ○, ●]]
    TypeFun.appFst(f1, a1)
  }

  def diag: TypeTag[[x] =>> (x, x)] =
    TypeFun(Routing.dup[●], TypeExpr.pair)

  def toType[A](ta: TypeTag[A]): Type[Nothing] =
    TypeFun.toExpr((ta: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ○, ●]])

  def toTypeFun[F[_]](tf: TypeTag[F]): TypeFun[Nothing, ●, ●] =
    (tf: TypeFun[Nothing, ?, ?]).asInstanceOf[TypeFun[Nothing, ●, ●]]

  import scala.{quoted => sq}
  private def fromTypeParam[T](using t: sq.Type[T], q: sq.Quotes): sq.Expr[TypeTag[T]] = {
    import q.reflect._

    val repr = TypeRepr.of[T]
    val pos = repr.typeSymbol.pos
    (repr, pos) match {
      case (_, None) =>
        sys.error(s"${sq.Type.show[T]} does not look like a type parameter, because it does not have a source position.")
      case (TypeRef(NoPrefix(), name), Some(pos)) =>
        val file = pos.sourceFile.path
        val line = pos.startLine
        '{
          TypeFun.scalaTypeParam[Nothing, T](
            filename = ${sq.Expr(file)},
            line = ${sq.Expr(line)},
            name = ${sq.Expr(name)},
          )
        }
      case _ =>
        sys.error(repr.show + " does not look like a type parameter")
    }
  }

  inline def ofTypeParam[T]: TypeTag[T] =
    ${ fromTypeParam[T] }
}
