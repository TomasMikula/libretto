package libretto.typology.toylang.types

import libretto.typology.kinds.*
import libretto.typology.types.{Routing, TypeFun}

private type TypeCon[K, L] = TypeConstructor[ScalaTypeParam, K, L]

opaque type TypeTag[A <: AnyKind] = Type.Fun[ScalaTypeParam, Any, Any]

object TypeTag {
  def apply[A <: AnyKind](using a: TypeTag[A]): TypeTag[A] =
    a

  given unit: TypeTag[Unit]     = (Type.Fun.unit: Type.Fun[ScalaTypeParam, ○, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]
  given int: TypeTag[Int]       = (Type.Fun.int: Type.Fun[ScalaTypeParam, ○, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]
  given string: TypeTag[String] = (Type.Fun.string: Type.Fun[ScalaTypeParam, ○, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]

  given pair: TypeTag[Tuple2] =
    (Type.Fun.pair: Type.Fun[ScalaTypeParam, ● × ●, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]

  given pair[A, B](using a: TypeTag[A], b: TypeTag[B]): TypeTag[(A, B)] =
    (Type.Fun.pair(
      (a: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ○, ●]],
      (b: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ○, ●]],
    ): Type.Fun[ScalaTypeParam, ○, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]

  given pair1[A](using a: TypeTag[A]): TypeTag[(A, _)] =
    (Type.Fun.pair1(
      (a: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ○, ●]]
    ): Type.Fun[ScalaTypeParam, ●, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]

  given sum: TypeTag[Either] =
    (Type.Fun.sum: Type.Fun[ScalaTypeParam, ● × ●, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]

  given sum1[A](using a: TypeTag[A]): TypeTag[Either[A, _]] =
    (Type.Fun.sum1(
      (a: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ○, ●]]
    ): Type.Fun[ScalaTypeParam, ●, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]

  given fix[F[_]](using f: TypeTag[F]): TypeTag[Fix[F]] =
    (Type.Fun.fix(
      (f: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ●, ●]]
    ): Type.Fun[ScalaTypeParam, ○, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]

  given pfix[F[_, _]](using f: TypeTag[F]): TypeTag[[x] =>> Fix[F[x, _]]] =
    (Type.Fun.pfix(
      (f: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ● × ●, ●]]
    ): Type.Fun[ScalaTypeParam, ●, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]

  def compose[F[_], G[_]](f: TypeTag[F], g: TypeTag[G]): TypeTag[[x] =>> F[G[x]]] = {
    val f1 = (f: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ●, ●]]
    val g1 = (g: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ●, ●]]
    ((f1 ∘ g1): Type.Fun[ScalaTypeParam, ●, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]
  }

  def compose2[F[_], G[_, _]](f: TypeTag[F], g: TypeTag[G]): TypeTag[[x, y] =>> F[G[x, y]]] = {
    val f1 = (f: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ●, ●]]
    val g1 = (g: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ● × ●, ●]]
    ((f1 ∘ g1): Type.Fun[ScalaTypeParam, ● × ●, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]
  }

  def composeSnd[F[_, _], H[_]](f: TypeTag[F], h: TypeTag[H]): TypeTag[[x, y] =>> F[x, H[y]]] = {
    val f1 = (f: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ● × ●, ●]]
    val h1 = (h: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ●, ●]]
    (f1.applyTo(Type.Args(h1).inSnd[●]): Type.Fun[ScalaTypeParam, ● × ●, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]
  }

  def app[F[_], A](f: TypeTag[F], a: TypeTag[A]): TypeTag[F[A]] = {
    val f1 = (f: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ●, ●]]
    val a1 = (a: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ○, ●]]
    ((f1 ∘ a1): Type.Fun[ScalaTypeParam, ○, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]
  }

  def appFst[F[_, _], A](f: TypeTag[F], a: TypeTag[A]): TypeTag[F[A, _]] = {
    val f1 = (f: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ● × ●, ●]]
    val a1 = (a: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ○, ●]]
    (f1.applyTo(Type.Args.introFst(a1)): Type.Fun[ScalaTypeParam, ●, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]
  }

  def diag: TypeTag[[x] =>> (x, x)] =
    (Type.Fun.pair
      .applyTo(Type.Args.dup)
      : Type.Fun[ScalaTypeParam, ●, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]

  def toType[A](ta: TypeTag[A]): Type[ScalaTypeParam] =
    Type.Fun.toType((ta: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ○, ●]])

  def toTypeFun[F[_]](tf: TypeTag[F]): Type.Fun[ScalaTypeParam, ●, ●] =
    (tf: Type.Fun[ScalaTypeParam, Any, Any]).asInstanceOf[Type.Fun[ScalaTypeParam, ●, ●]]

  import scala.{quoted as sq}
  private def fromTypeParam[T](using t: sq.Type[T], q: sq.Quotes): sq.Expr[TypeTag[T]] = {
    import q.reflect.*

    val repr = TypeRepr.of[T]
    val pos = repr.typeSymbol.pos
    (repr, pos) match {
      case (_, None) =>
        sys.error(s"${sq.Type.show[T]} does not look like a type parameter, because it does not have a source position.")
      case (TypeRef(NoPrefix(), name), Some(pos)) =>
        val file = pos.sourceFile.path
        val line = pos.startLine
        '{
          (Type.Fun.abstractType(
            ScalaTypeParam(
              filename = ${sq.Expr(file)},
              line = ${sq.Expr(line)},
              name = ${sq.Expr(name)},
            )
          ): Type.Fun[ScalaTypeParam, ○, ●]).asInstanceOf[Type.Fun[ScalaTypeParam, Any, Any]]
        }
      case _ =>
        sys.error(repr.show + " does not look like a type parameter")
    }
  }

  inline def ofTypeParam[T]: TypeTag[T] =
    ${ fromTypeParam[T] }
}
