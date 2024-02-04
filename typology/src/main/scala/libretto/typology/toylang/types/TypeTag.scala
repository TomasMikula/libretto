package libretto.typology.toylang.types

import libretto.typology.kinds.*
import libretto.typology.types.{Routing, TypeFun}

private type TypeCon[K, L] = TypeConstructor[ScalaTypeParam, K, L]

opaque type TypeTag[A <: AnyKind] = TypeFun[TypeCon, ?, ?]

object TypeTag {
  def apply[A <: AnyKind](using a: TypeTag[A]): TypeTag[A] =
    a

  given unit: TypeTag[Unit] = Type.Fun.unit
  given int: TypeTag[Int] = Type.Fun.int
  given string: TypeTag[String] = Type.Fun.string

  given pair: TypeTag[Tuple2] =
    Type.Fun.pair

  given pair[A, B](using a: TypeTag[A], b: TypeTag[B]): TypeTag[(A, B)] =
    Type.Fun.pair(
      (a: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ○, ●]],
      (b: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ○, ●]],
    )

  given pair1[A](using a: TypeTag[A]): TypeTag[(A, _)] =
    Type.Fun.pair1(
      (a: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ○, ●]]
    )

  given sum: TypeTag[Either] =
    Type.Fun.sum

  given sum1[A](using a: TypeTag[A]): TypeTag[Either[A, _]] =
    Type.Fun.sum1(
      (a: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ○, ●]]
    )

  given fix[F[_]](using f: TypeTag[F]): TypeTag[Fix[F]] =
    Type.Fun.fix(
      (f: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ●, ●]]
    )

  given pfix[F[_, _]](using f: TypeTag[F]): TypeTag[[x] =>> Fix[F[x, _]]] =
    Type.Fun.pfix(
      (f: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ● × ●, ●]]
    )

  def compose[F[_], G[_]](f: TypeTag[F], g: TypeTag[G]): TypeTag[[x] =>> F[G[x]]] = {
    val f1 = (f: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ●, ●]]
    val g1 = (g: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ●, ●]]
    f1 ∘ g1
  }

  def compose2[F[_], G[_, _]](f: TypeTag[F], g: TypeTag[G]): TypeTag[[x, y] =>> F[G[x, y]]] = {
    val f1 = (f: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ●, ●]]
    val g1 = (g: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ● × ●, ●]]
    f1 ∘ g1
  }

  def composeSnd[F[_, _], H[_]](f: TypeTag[F], h: TypeTag[H]): TypeTag[[x, y] =>> F[x, H[y]]] = {
    val f1 = (f: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ● × ●, ●]]
    val h1 = (h: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ●, ●]]
    TypeFun.composeSnd(f1, h1)
  }

  def app[F[_], A](f: TypeTag[F], a: TypeTag[A]): TypeTag[F[A]] = {
    val f1 = (f: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ●, ●]]
    val a1 = (a: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ○, ●]]
    TypeFun.fromExpr(f1(toType(a1)))
  }

  def appFst[F[_, _], A](f: TypeTag[F], a: TypeTag[A]): TypeTag[F[A, _]] = {
    val f1 = (f: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ● × ●, ●]]
    val a1 = (a: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ○, ●]]
    TypeFun.appFst(f1, a1)
  }

  def diag: TypeTag[[x] =>> (x, x)] =
    TypeFun(Routing.dup[●], Type.Fun.pair)

  def toType[A](ta: TypeTag[A]): Type[ScalaTypeParam] =
    TypeFun.toExpr((ta: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ○, ●]])

  def toTypeFun[F[_]](tf: TypeTag[F]): TypeFun[TypeCon, ●, ●] =
    (tf: TypeFun[TypeCon, ?, ?]).asInstanceOf[TypeFun[TypeCon, ●, ●]]

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
          Type.Fun.abstractType(
            ScalaTypeParam(
              filename = ${sq.Expr(file)},
              line = ${sq.Expr(line)},
              name = ${sq.Expr(name)},
            )
          )
        }
      case _ =>
        sys.error(repr.show + " does not look like a type parameter")
    }
  }

  inline def ofTypeParam[T]: TypeTag[T] =
    ${ fromTypeParam[T] }
}
