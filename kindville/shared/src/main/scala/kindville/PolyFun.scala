package kindville

import kindville.Reporting.*
import scala.annotation.experimental
import scala.quoted.*

private object PolyFun {

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
  def apply(using Quotes)(
    tParamNames: List[String],
    tParamBounds: (Int => qr.TypeRepr) => List[qr.TypeBounds],
    vParamNames: List[String],
    vParamTypes: List[qr.TypeRepr] => List[qr.TypeRepr],
    returnType: List[qr.TypeRepr] => qr.TypeRepr,
    body: (List[qr.TypeRepr], List[qr.Term], qr.Symbol) => qr.Term,
    owner: qr.Symbol = qr.Symbol.spliceOwner,
  ): qr.Term = {
    import qr.*

    val methSym =
      Symbol.newMethod(
        owner,
        name = "polyFunImpl",
        tpe = polyFunApplyMethodType(tParamNames, tParamBounds, vParamNames, vParamTypes, returnType)
      )

    val meth =
      DefDef(
        methSym,
        rhsFn = { case List(targTrees, argTrees) =>
          val targs = targTrees.map(_.asInstanceOf[TypeTree].tpe)
          val args  = argTrees.map(_.asInstanceOf[Term])
          Some(body(targs, args, methSym))
        },
      )

    Block(
      List(meth),
      Closure(Ident(methSym.termRef), tpe = None)
    )
  }

  def unapply(using Quotes)(expr: qr.Term): Option[(
    List[(String, Either[qr.TypeBounds, qr.LambdaTypeTree], qr.TypeRef)], // type params: (name, kind, reference)
    List[(String, qr.TypeTree, qr.TermRef)], // value params
    qr.TypeTree,                             // return type
    qr.Term,                                 // body
  )] = {
    import qr.*

    expr match
      case Block(List(stmt), Closure(method, optTp)) =>
        (stmt, method) match
          case (DefDef(name, paramss, retTp, Some(body)), Ident(methodName)) if methodName == name =>
            paramss match
              case TypeParamClause(tparams) :: TermParamClause(params) :: Nil =>
                Some((
                  tparams.map { case t @ TypeDef(name, kind) =>
                    kind match
                      case b: TypeBoundsTree => (name, Left(b.tpe), t.symbol.typeRef)
                      case l: LambdaTypeTree => (name, Right(l), t.symbol.typeRef)
                      case other => assertionFailed(s"Unexpected representation of $name's kind: ${treeStruct(kind)}")
                  },
                  params.map { case v @ ValDef(name, tpe, _) => (name, tpe, v.symbol.termRef) },
                  retTp,
                  body,
                ))
              case _ =>
                None
          case _ =>
            None
      case _ =>
        None
  }

  private def polyFunApplyMethodType(using Quotes)(
    tParamNames: List[String],
    tParamBounds: (Int => qr.TypeRepr) => List[qr.TypeBounds],
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
      pt => tParamBounds(pt.param),
      pt => MethodType(
        vParamNames,
      )(
        mt => vParamTypes(pt.params(nTypeParams)),
        mt => returnType(pt.params(nTypeParams)),
      ),
    )
  }

}
