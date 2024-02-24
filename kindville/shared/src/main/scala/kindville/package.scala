package kindville

import scala.quoted.*
import scala.PolyFunction
import scala.annotation.experimental

sealed trait *
sealed trait ->[K, L]

sealed trait ::[H <: AnyKind, T]
sealed trait TNil

sealed trait ofKind[F <: AnyKind, K]
sealed trait ofKinds[As, Ks]

private transparent inline def qr(using Quotes): quotes.reflect.type =
  quotes.reflect

extension [FA](fa: FA)
  transparent inline def unmask[F <: AnyKind, As](using ev: TypeApp[F, As, FA]): Any =
    ${ unmaskImpl('fa, 'ev) }

  /** Returns `[R] => ([A1, ...] => F[A1, ...] => R) => R`. */
  @experimental
  transparent inline def visit[F <: AnyKind, As](using TypeApp[F, As, FA]): Any =
    ${ visitImpl[F, FA]('fa) }

extension (f: PolyFunction)
  transparent inline def at[As]: Nothing => Any =
    ${ atImpl[As]('f) }

private def atImpl[As](f: Expr[PolyFunction])(using
  Quotes,
  Type[As],
): Expr[Nothing => Any] =
  import quotes.reflect.*

  Select
    .unique(f.asTerm, "apply")
    .appliedToTypes(decodeTypeArgs(Type.of[As]).map(TypeRepr.of(using _)))
    .etaExpand(Symbol.spliceOwner)
    .asExprOf[Nothing => Any]

/** Returns `[A1, ...] => F[A1, ...] => R`. */
@experimental
transparent inline def encoderOf[F <: AnyKind, R](
  f: [As, FAs] => (FAs, TypeApp[F, As, FAs]) => R,
): PolyFunction =
  ${ encoderImpl[F, R]('f) }

@experimental
private[kindville] def encoderImpl[F <: AnyKind, R](
  f: Expr[[As, FAs] => (FAs, TypeApp[F, As, FAs]) => R],
)(using
  Quotes,
  Type[F],
  Type[R],
): Expr[PolyFunction] = {
  import quotes.reflect.*

  TypeRepr.of[F] match
    case bindingType @ TypeLambda(paramNames, paramBounds, body) =>
      polyFun(
        tParamNames  = paramNames,
        tParamBounds = _ => paramBounds, // TODO: must perform substitution in order to work for interdependent type params
        vParamNames  = List("f"),
        vParamTypes  = tParams => List(bindingType.appliedTo(tParams)),
        returnType   = _ => TypeRepr.of[R],
        body =
          (targs, args) =>
            val tAs = encodeTypeArgs(targs)
            val tFAs = AppliedType(TypeRepr.of[F], targs)
            val List(fas) = args

            // f[As, FAs](fas, TypeApp[F, FAs])
            polyFunApply(f.asTerm)(tAs, tFAs)(
              fas,
              TypeApp.inferArgsImpl(using
                quotes,
                Type.of[F],
                tFAs.asType.asInstanceOf[Type[Any]],
              ).asTerm,
            )
      ).asExprOf[PolyFunction]

    case other =>
      val fs = Printer.TypeReprShortCode.show(other)
      // val fs = Printer.TypeReprStructure.show(other)
      report.error(s"Implementation restriction: works only for type lambdas. Please, eta-expand $fs to a type lambda manually.")
      '{ ??? }
}

@experimental
private def visitImpl[F <: AnyKind, FAs](value: Expr[FAs])(using
  Quotes,
  Type[F],
  Type[FAs],
): Expr[Any] = {
  import quotes.reflect.*

  TypeRepr.of[F] match
    case tf @ TypeLambda(paramNames, paramBounds, body) =>
      polyFun(
        tParamNames = List("R"),
        tParamBounds = _ => List(TypeBounds.empty),
        vParamNames = List("f"),
        vParamTypes = outerTParams => List(
          polyFunType(
            paramNames,
            _ => paramBounds,  // TODO: must perform substitution in order to work for interdependent type params
            vParamNames = List("fa"),
            vParamTypes = tparams => List(tf.appliedTo(tparams)),
            returnType = _ => outerTParams.head,
          )
        ),
        returnType = tparams => tparams.head,
        body = (typeArgs, args) => {
          val List(r) = typeArgs
          val List(f) = args
          val fFakeType =
            polyFunType(List("Dummy"), _ => List(TypeBounds.empty), List("fa"), _ => List(TypeRepr.of[FAs]), _ => r)
          val f1: Expr[[Dummy] => FAs => Any] =
            Typed(f,  TypeTree.of(using fFakeType.asType)).asExprOf[[Dummy] => FAs => Any]
          '{ $f1($value.asInstanceOf) }.asTerm
        },
      ).asExpr

    case other =>
      val fStr = Printer.TypeReprShortCode.show(other)
      report.error(s"Implementation restriction: works only for type lambdas. Please, eta-expand $fStr to a type lambda manually.")
      '{ ??? }
}

private def polyFunApply(using Quotes)(f: qr.Term)(targs: qr.TypeRepr*)(args: qr.Term*): qr.Term =
  qr.Select
    .unique(f, "apply")
    .appliedToTypes(targs.toList)
    .appliedToArgs(args.toList)

private def polyFunApplyMethodType(using Quotes)(
  tParamNames: List[String],
  tParamBounds: qr.PolyType => List[qr.TypeBounds],
  vParamNames: List[String],
  vParamTypes: List[qr.TypeRepr] => List[qr.TypeRepr],
  returnType: List[qr.TypeRepr] => qr.TypeRepr,
): qr.PolyType = {
  import qr.*

  extension (pt: PolyType)
    def params(n: Int): List[TypeRepr] =
      List.range(0, n).map(pt.param(_))

  val nTypeParams = tParamNames.length

  PolyType(tParamNames)(
    tParamBounds,
    pt => MethodType(
      vParamNames,
    )(
      mt => vParamTypes(pt.params(nTypeParams)),
      mt => returnType(pt.params(nTypeParams)),
    ),
  )
}

private def polyFunType(using Quotes)(
  tParamNames: List[String],
  tParamBounds: qr.PolyType => List[qr.TypeBounds],
  vParamNames: List[String],
  vParamTypes: List[qr.TypeRepr] => List[qr.TypeRepr],
  returnType: List[qr.TypeRepr] => qr.TypeRepr,
): qr.TypeRepr =
  qr.Refinement(
    qr.TypeRepr.of[PolyFunction],
    "apply",
    polyFunApplyMethodType(tParamNames, tParamBounds, vParamNames, vParamTypes, returnType)
  )

/**
  *
  *
  * @param tParamNames
  * @param tParamBounds
  * @param vParamTypes function that, given type parameters, constructs the types of value parameters
  * @param returnType function that, given type parameters, constructs the return type
  * @param body
  * @return
  */
@experimental
private def polyFun(using Quotes)(
  tParamNames: List[String],
  tParamBounds: qr.PolyType => List[qr.TypeBounds],
  vParamNames: List[String],
  vParamTypes: List[qr.TypeRepr] => List[qr.TypeRepr],
  returnType: List[qr.TypeRepr] => qr.TypeRepr,
  body: (List[qr.TypeRepr], List[qr.Term]) => qr.Term,
): qr.Term = {
  import qr.*

  val parents =
    List(TypeTree.of[Object], TypeTree.of[PolyFunction])

  val clsSym =
    Symbol.newClass(
      Symbol.spliceOwner,
      name = "$anon",
      parents = parents.map(_.tpe),
      decls = cls => List(
        Symbol.newMethod(
          cls,
          "apply",
          polyFunApplyMethodType(tParamNames, tParamBounds, vParamNames, vParamTypes, returnType),
        ),
      ),
      selfType = None,
    )

  val applySym =
    clsSym.declaredMethod("apply").head

  val applyDef =
    DefDef(
      applySym,
      argss => {
        val List(targs, args) = argss
        val typeArgs: List[TypeRepr] = targs.map(_.asInstanceOf[TypeTree].tpe)
        val valArgs: List[Term] = args.map(_.asExpr.asTerm)
        Some(body(typeArgs, valArgs))
      },
    )

  val clsDef = ClassDef(clsSym, parents, List(applyDef))
  val newCls = Apply(Select(New(TypeIdent(clsSym)), clsSym.primaryConstructor), args = Nil)

  Block(
    List(clsDef),
    newCls,
  )
}

private[kindville] def unmaskImpl[F <: AnyKind, As, FA](
  fa: Expr[FA],
  ev: Expr[TypeApp[F, As, FA]],
)(using
  Quotes,
  Type[F],
  Type[As],
): Expr[Any] =
  import quotes.reflect.*
  val targs: List[Type[?]] = decodeTypeArgs[As](Type.of[As])
  cast(fa, Type.of[F], targs)

private[kindville] def encodeTypeArgs(using Quotes)(args: List[quotes.reflect.TypeRepr]): quotes.reflect.TypeRepr =
  import quotes.reflect.*
  args match
    case Nil => TypeRepr.of[TNil]
    case t :: ts => TypeRepr.of[::].appliedTo(List(t, encodeTypeArgs(ts)))

private[kindville] def decodeTypeArgs[As <: AnyKind](args: Type[As])(using Quotes): List[Type[?]] =
  import quotes.reflect.*

  val cons = TypeRepr.of[::]

  args match
    case '[TNil] => Nil
    case other =>
      val repr = TypeRepr.of(using other)
      repr match
        case AppliedType(f, args) =>
          f.asType match
            case '[::] =>
              args match
                case h :: t :: Nil =>
                  h.asType :: decodeTypeArgs(t.asType)(using quotes)
                case _ =>
                  report.errorAndAbort(s"Unexpected number of type arguments to ${Printer.TypeReprShortCode.show(f)}. Expected 2, got ${args.size}: ${args.map(Printer.TypeReprShortCode.show(_).mkString(", "))}")
            case other =>
              report.error(s"Cannot decode a list of type arguments from type ${Printer.TypeReprShortCode.show(repr)}")
              Nil
        case other =>
          report.error(s"Cannot decode a list of type arguments from type ${Printer.TypeReprShortCode.show(repr)}")
          Nil

private[kindville] def cast[FA, F <: AnyKind](
  expr: Expr[FA],
  tf: Type[F],
  targs: List[Type[?]],
)(using Quotes): Expr[Any] =
  import quotes.reflect.*

  val resultType: Type[?] =
    TypeRepr.of(using tf)
      .appliedTo(targs.map(TypeRepr.of(using _)))
      .asType

  expr.asExprOf(using resultType.asInstanceOf[Type[Any]])

private[kindville] inline def termStructureOf[A](a: A): String =
  ${ printTermStructure('a) }

private[kindville] inline def typeStructureOf[A <: AnyKind]: String =
  ${ printTypeStructure[A] }

private def printTermStructure[A](a: Expr[A])(using Quotes): Expr[String] =
  import quotes.reflect.*
  Expr(Printer.TreeStructure.show(a.asTerm))


private def printTypeStructure[A <: AnyKind](using Quotes, Type[A]): Expr[String] =
  import quotes.reflect.*
  TypeRepr.of[A] match
    case TypeLambda(_, _, AppliedType(_, args)) =>
      Expr(args.collect { case ParamRef(binder, _) => Printer.TypeReprStructure.show(binder) }.head)
    case _ =>
      Expr(Printer.TypeReprStructure.show(TypeRepr.of[A]))


def foo[A]: FooSyntax[A] =
  new FooSyntax[A]

class FooSyntax[A]:
  inline def bar[B]: String =
    ${ barImpl[A, B] } // I want to deliver Type[A] captured by the call to foo[A]

def barImpl[A, B](using Quotes, Type[A], Type[B]): Expr[String] =
  import quotes.reflect.*
  Expr(Printer.TypeReprStructure.show(TypeRepr.of[A]))