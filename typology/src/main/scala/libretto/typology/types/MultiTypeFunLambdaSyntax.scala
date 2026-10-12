package libretto.typology.types

import libretto.lambda.{CapturingFun, Lambdas, PreparedArrowModule}
import libretto.lambda.util.SourcePos
import libretto.lambda.util.Validated.{Invalid, Valid}
import libretto.typology.kinds.*

/** Lambda syntax for type functions between non-empty kinds.
  *
  * Obtain a module using `MultiTypeFun.lambdaSyntax[TC]` and import its members:
  * {{{
  * val syntax = MultiTypeFun.lambdaSyntax[TC]
  * import syntax.*
  * val duplicate = lambda[●, ● × ●] { a => a zip a }
  * }}}
  *
  * Variables may be duplicated or discarded. Closed type functions with input
  * kind `○` can be introduced using `const`; expression kinds themselves are non-empty.
  */
final class MultiTypeFunLambdaSyntax[TC[_, _]] private[types] () {
  private case class Origin(description: String, pos: SourcePos) {
    override def toString: String = s"$description at ${pos.filename}:${pos.line}"
  }

  private val prepared: PreparedArrowModule[KindN, MultiTypeFun[TC, _, _], ×] =
    new PreparedArrowModule[KindN, MultiTypeFun[TC, _, _], ×]
  import prepared.{Prepared, given}

  private val lambdas: Lambdas[Prepared, ×, Origin, SourcePos] = Lambdas(
    universalSplit = Some([K] => (_: DummyImplicit) ?=> Prepared[K, K × K] { k =>
      (MultiTypeFun.dup[TC, K](using k), k × k)
    }),
    universalDiscard = Some([K, L] => (_: DummyImplicit) ?=> (
      Prepared[K × L, L] { kl =>
        val (k, l) = KindN.unpair(kl)
        (MultiTypeFun.elimFst[TC, K, L](using k, l), l)
      },
      Prepared[L × K, L] { lk =>
        val (l, k) = KindN.unpair(lk)
        (MultiTypeFun.elimSnd[TC, L, K](using l, k), l)
      },
    )),
  )

  private case class Expression[K](value: lambdas.Expr[K], kind: KindN[K])
  opaque type Expr[K] = Expression[K]
  opaque type LambdaContext = lambdas.Context

  def lambda[K, L](f: LambdaContext ?=> Expr[K] => Expr[L])(using
    k: KindN[K],
    pos: SourcePos,
  ): MultiTypeFun[TC, K, L] =
    lambdas.delambdifyFoldTopLevel[K, L](
      pos, Origin("Lambda parameter", pos), a => f(Expression(a, k)).value,
    ) match {
      case Valid(CapturingFun.NoCapture(f)) => f.run(k)._1
      case Valid(CapturingFun.Closure(captured, _)) =>
        val vars = lambdas.Expr.initialVars(captured).list
        throw IllegalArgumentException(s"Undefined variables: ${vars.map(_.origin).mkString(", ")}")
      case Invalid(errors) =>
        throw IllegalArgumentException(s"$errors")
    }

  extension [K, L](f: MultiTypeFun[TC, K, L]) {
    def apply(a: Expr[K])(using ctx: LambdaContext, l: KindN[L], pos: SourcePos): Expr[L] =
      Expression(lambdas.Expr.map(a.value, prepared.lift(f))(Origin("Function result", pos)), l)
  }

  extension [K, L](f: TypeFun[TC, K, L]) {
    def apply(a: Expr[K])(using ctx: LambdaContext, pos: SourcePos): Expr[L] =
      MultiTypeFun(f).apply(a)(using ctx, KindN(f.outKind), pos)
  }

  extension [K, L](f: TypeExpr[TC, K, L]) {
    def apply(a: Expr[K])(using ctx: LambdaContext, pos: SourcePos): Expr[L] =
      val l = KindN(f.outKind)
      Expression(
        lambdas.Expr.map(a.value, prepared.lift(MultiTypeFun(f))(using l))(Origin("Type expression result", pos)),
        l,
      )
  }

  extension [K](a: Expr[K]) {
    def kind: KindN[K] = a.kind

    infix def zip[L](b: Expr[L])(using ctx: LambdaContext, pos: SourcePos): Expr[K × L] =
      Expression(lambdas.Expr.zip(a.value, b.value)(Origin("Pair", pos)), a.kind × b.kind)
  }

  extension [K, L](ab: Expr[K × L]) {
    def unzip(using ctx: LambdaContext, pos: SourcePos): (Expr[K], Expr[L]) =
      val (k, l) = KindN.unpair(ab.kind)
      val (a, b) = lambdas.Expr.unzip(ab.value)(Origin("First component", pos), Origin("Second component", pos))
      (Expression(a, k), Expression(b, l))
  }

  object zip {
    def unapply[K, L](ab: Expr[K × L])(using LambdaContext, SourcePos): (Expr[K], Expr[L]) =
      ab.unzip
  }

  def const[K](f: MultiTypeFun[TC, ○, K])(using ctx: LambdaContext, k: KindN[K], pos: SourcePos): Expr[K] =
    val value = lambdas.Expr.const[K](
      [X] => (_: DummyImplicit) ?=> Prepared[X, K × X] { x =>
        (MultiTypeFun.introFst[TC, K, X](f)(using k, x), k × x)
      },
      [X] => (_: DummyImplicit) ?=> Prepared[X, X × K] { x =>
        (MultiTypeFun.introSnd[TC, X, K](f)(using x, k), x × k)
      },
    )(Origin("Constant", pos))
    Expression(value, k)

  def const[K](f: TypeFun[TC, ○, K])(using ctx: LambdaContext, pos: SourcePos): Expr[K] =
    const(MultiTypeFun(f))(using ctx, KindN(f.outKind), pos)

  def const[K](f: TypeExpr[TC, ○, K])(using ctx: LambdaContext, pos: SourcePos): Expr[K] =
    const(MultiTypeFun(f))(using ctx, KindN(f.outKind), pos)
}
