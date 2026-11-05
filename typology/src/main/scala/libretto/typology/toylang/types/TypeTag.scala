package libretto.typology.toylang.types

import libretto.typology.kinds.*

opaque type TypeTag[A <: AnyKind] = Type.Fun[Nothing, Any, Any]

object TypeTag {
  def apply[A <: AnyKind](using a: TypeTag[A]): TypeTag[A] =
    a

  given unit: TypeTag[Unit]     = (Type.Fun.unit: Type.Fun[Nothing, ○, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]
  given int: TypeTag[Int]       = (Type.Fun.int: Type.Fun[Nothing, ○, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]
  given string: TypeTag[String] = (Type.Fun.string: Type.Fun[Nothing, ○, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]

  given pair: TypeTag[Tuple2] =
    (Type.Fun.pair: Type.Fun[Nothing, ● × ●, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]

  given pair[A, B](using a: TypeTag[A], b: TypeTag[B]): TypeTag[(A, B)] =
    (Type.Fun.pair(
      (a: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ○, ●]],
      (b: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ○, ●]],
    ): Type.Fun[Nothing, ○, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]

  given pair1[A](using a: TypeTag[A]): TypeTag[(A, _)] =
    (Type.Fun.pair1(
      (a: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ○, ●]]
    ): Type.Fun[Nothing, ●, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]

  given sum: TypeTag[Either] =
    (Type.Fun.sum: Type.Fun[Nothing, ● × ●, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]

  given sum1[A](using a: TypeTag[A]): TypeTag[Either[A, _]] =
    (Type.Fun.sum1(
      (a: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ○, ●]]
    ): Type.Fun[Nothing, ●, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]

  given fix[F[_]](using f: TypeTag[F]): TypeTag[Fix[F]] =
    (Type.Fun.fix(
      (f: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ●, ●]]
    ): Type.Fun[Nothing, ○, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]

  given pfix[F[_, _]](using f: TypeTag[F]): TypeTag[[x] =>> Fix[F[x, _]]] =
    (Type.Fun.pfix(
      (f: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ● × ●, ●]]
    ): Type.Fun[Nothing, ●, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]

  def compose[F[_], G[_]](f: TypeTag[F], g: TypeTag[G]): TypeTag[[x] =>> F[G[x]]] = {
    val f1 = (f: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ●, ●]]
    val g1 = (g: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ●, ●]]
    ((f1 ∘ g1): Type.Fun[Nothing, ●, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]
  }

  def compose2[F[_], G[_, _]](f: TypeTag[F], g: TypeTag[G]): TypeTag[[x, y] =>> F[G[x, y]]] = {
    val f1 = (f: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ●, ●]]
    val g1 = (g: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ● × ●, ●]]
    ((f1 ∘ g1): Type.Fun[Nothing, ● × ●, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]
  }

  def composeSnd[F[_, _], H[_]](f: TypeTag[F], h: TypeTag[H]): TypeTag[[x, y] =>> F[x, H[y]]] = {
    val f1 = (f: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ● × ●, ●]]
    val h1 = (h: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ●, ●]]
    (f1.applyTo(Type.Args(h1).inSnd[●]): Type.Fun[Nothing, ● × ●, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]
  }

  def app[F[_], A](f: TypeTag[F], a: TypeTag[A]): TypeTag[F[A]] = {
    val f1 = (f: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ●, ●]]
    val a1 = (a: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ○, ●]]
    ((f1 ∘ a1): Type.Fun[Nothing, ○, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]
  }

  def appFst[F[_, _], A](f: TypeTag[F], a: TypeTag[A]): TypeTag[F[A, _]] = {
    val f1 = (f: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ● × ●, ●]]
    val a1 = (a: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ○, ●]]
    (f1.applyTo(Type.Args.introFst(a1)): Type.Fun[Nothing, ●, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]
  }

  def diag: TypeTag[[x] =>> (x, x)] =
    (Type.Fun.pair
      .applyTo(Type.Args.dup)
      : Type.Fun[Nothing, ●, ●]).asInstanceOf[Type.Fun[Nothing, Any, Any]]

  def toType[A](ta: TypeTag[A]): Type[Nothing] =
    Type.Fun.toType((ta: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ○, ●]])

  def toTypeFun[F[_]](tf: TypeTag[F]): Type.Fun[Nothing, ●, ●] =
    (tf: Type.Fun[Nothing, Any, Any]).asInstanceOf[Type.Fun[Nothing, ●, ●]]
}
