package libretto.typology.toylang.typeinfer

import libretto.lambda.{MappedMorphism, MonoidalObjectMap, SymmetricMonoidalCategory, UnhandledCase}
import libretto.lambda.util.{SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.util.unapply.Unapply
import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.dsl.{|| as |}
import libretto.typology.inference.TypeOps
import libretto.typology.kinds.{Kinds, KindN, ×, ○, ●}
import libretto.typology.toylang.terms.TypedFun
import libretto.typology.toylang.types
import libretto.typology.toylang.types.{Label, ScalaTypeParam, Type, TypeConstructor, TypeTag}
import libretto.typology.types.{Routing, TypeExpr, TypeFun}

private[typeinfer] type KindMismatch[Types] = Types |*| Types

private[typeinfer] type TypesF[T, X] = OneOf
  [ "singleType" :: T
  | "prod" :: (X |*| X)
  | "kindMismatch" :: KindMismatch[X]
  ]

private[typeinfer] type Types[T] = Rec[TypesF[T, _]]

private[typeinfer] object Types {
  def pack[T]: TypesF[T, Types[T]] -⚬ Types[T] = dsl.pack[TypesF[T, _]]

  def singleType[T]: T -⚬ Types[T] = pack ∘ OneOf.inject("singleType")
  def prod[T]: (Types[T] |*| Types[T]) -⚬ Types[T] = pack ∘ OneOf.inject("prod")
  def kindMismatch[T]: (Types[T] |*| Types[T]) -⚬ Types[T] = pack ∘ OneOf.inject("kindMismatch")

  object SingleType:
    def unapply[T](ts: $[Types[T]])(using SourcePos, LambdaContext): Some[$[T]] =
      Some(ts.unpackedMatchAgainst(OneOf.partition[TypesF[T, Types[T]]]["singleType"]))

  object Prod:
    def unapply[T](ts: $[Types[T]])(using SourcePos, LambdaContext): Some[$[Types[T] |*| Types[T]]] =
      Some(ts.unpackedMatchAgainst(OneOf.partition[TypesF[T, Types[T]]]["prod"]))

  object KindMismatch:
    def unapply[T](ts: $[Types[T]])(using SourcePos, LambdaContext): Some[$[KindMismatch[Types[T]]]] =
      Some(ts.unpackedMatchAgainst(OneOf.partition[TypesF[T, Types[T]]]["kindMismatch"]))

  def map[T, U](f: T -⚬ U): Types[T] -⚬ Types[U] =
    rec { self =>
      λ { ts =>
        switch(ts)
          .is { case KindMismatch(x |*| y) => kindMismatch(self(x) |*| self(y)) }
          .is { case SingleType(t) => singleType(f(t)) }
          .is { case Prod(ts1 |*| ts2) => prod(self(ts1) |*| self(ts2)) }
          .end
      }
    }

  def splitMap[T, U, V](f: T -⚬ (U |*| V)): Types[T] -⚬ (Types[U] |*| Types[V]) =
    rec { self =>
      λ { ts =>
        switch(ts)
          .is { case KindMismatch(mismatch) =>
            val x |*| y = mismatch
            val xu |*| xv = self(x)
            val yu |*| yv = self(y)
            kindMismatch(xu |*| yu) |*| kindMismatch(xv |*| yv)
          }
          .is { case SingleType(t) => f(t) :>> par(singleType, singleType) }
          .is { case Prod(ts1 |*| ts2) => (self(ts1) |*| self(ts2)) > IXI > par(prod, prod) }
          .end
      }
    }

  def mapWith[X, T, U](f: (X |*| T) -⚬ U)(using Cosemigroup[X]): (X |*| Types[T]) -⚬ Types[U] =
    rec { self =>
      λ { case +(x) |*| ts =>
        switch(ts)
          .is { case KindMismatch(p |*| q) => kindMismatch(self(x |*| p) |*| self(x |*| q)) }
          .is { case SingleType(t) => singleType(f(x |*| t)) }
          .is { case Prod(ts1 |*| ts2) => prod(self(x |*| ts1) |*| self(x |*| ts2)) }
          .end
      }
    }

  def merge[T](f: (T |*| T) -⚬ T): (Types[T] |*| Types[T]) -⚬ Types[T] =
    rec { self =>
      λ { case ts |*| us =>
        switch(ts |*| us)
          .is { case SingleType(t) |*| SingleType(u) => singleType(f(t |*| u)) }
          .is { case Prod(t1 |*| t2) |*| Prod(u1 |*| u2) => prod(self(t1 |*| u1) |*| self(t2 |*| u2)) }
          .is { case ts |*| us => kindMismatch(ts |*| us) }
          .end
      }
    }

  def output[T](
    outputElem: T -⚬ Val[Type[Label]],
  ): Types[T] -⚬ Val[types.Types[Label]] =
    rec { self =>
      λ { ts =>
        switch(ts)
          .is { case SingleType(t) =>
            outputElem(t) :>> mapVal { types.Types.SingleType(_) }
          }
          .is { case Prod(ts |*| us) =>
            (self(ts) ** self(us)) :>> mapVal { case (ts, us) => types.Types.Product(ts, us) }
          }
          .is { case KindMismatch(x |*| y) =>
            (self(x) ** self(y)) :>> mapVal { case (x, y) => types.Types.KindMismatch(x, y) }
          }
          .end
      }
    }

  def close[T](
    closeElem: T -⚬ Done,
  ): Types[T] -⚬ Done =
    rec { self =>
      λ { ts =>
        switch(ts)
          .is { case SingleType(t) => closeElem(t) }
          .is { case Prod(t |*| u) => join(self(t) |*| self(u)) }
          .is { case KindMismatch(x |*| y) => join(self(x) |*| self(y)) }
          .end
      }
    }
}

private[typeinfer] type FixOrPFix[T] = OneOf
  [ "fix" :: Val[TypeConstructor.Fix[ScalaTypeParam, ?]]

  // Parameterized fixed point.
  // The nesting of the types must correspond to the kinds of PFix type parameters.
  // Once Libretto has existentials, can use them to ensure well-kindedness statically.
  | "pfix" :: (Val[TypeConstructor.PFix[ScalaTypeParam, ?, ?]] |*| Types[T])
  ]

private[typeinfer] type NonAbstractTypeF[V, T, X] = OneOf
  [ "error" :: NonAbstractType.TypeError[V, X]
  | "unit" ::  Done
  | "int" :: Done
  | "string" :: Done
  | "recType" :: FixOrPFix[T]
  | "recCall" :: (T |*| T)
  | "either" :: (T |*| T)
  | "pair" :: (T |*| T)
  ]

private[typeinfer] type NonAbstractType[V, T] = Rec[NonAbstractTypeF[V, T, _]]

private[typeinfer] object NonAbstractType {
  type TypeError[V, X] = OneOf
    [ "mismatch" :: (X |*| X)
    | "selfRef" :: V // forbidden self-reference
    ]

  private def pack[V, T]: NonAbstractTypeF[V, T, NonAbstractType[V, T]] -⚬ NonAbstractType[V, T] =
    dsl.pack

  private def unpack[V, T]: NonAbstractType[V, T] -⚬ NonAbstractTypeF[V, T, NonAbstractType[V, T]] =
    dsl.unpack

  private def inject[V, T](using
    u: Unapply[NonAbstractTypeF[V, T, NonAbstractType[V, T]], OneOf],
  )(
    label: String,
  )(using
    i: OneOf.IsCaseOf[label.type, u.A]
  ): i.Type -⚬ NonAbstractTypeF[V, T, NonAbstractType[V, T]] =
    OneOf
      .inject(label)
      .to(using u.ev.flip)

  private def partition[V, T](using
    u: Unapply[NonAbstractTypeF[V, T, NonAbstractType[V, T]], OneOf],
    cs: OneOf.CaseList[u.A],
  ): OneOf.Partitioning[u.A] =
    OneOf.partition[NonAbstractTypeF[V, T, NonAbstractType[V, T]]]

  def pair[V, T]: (T |*| T) -⚬ NonAbstractType[V, T] =
    pack ∘ inject[V, T]("pair")

  object Pair:
    def unapply[V, T](t: $[NonAbstractType[V, T]])(using SourcePos, LambdaContext): Some[$[T |*| T]] =
      Some(t.unpackedMatchAgainst(partition[V, T]["pair"]))

  def either[V, T]: (T |*| T) -⚬ NonAbstractType[V, T] =
    pack ∘ inject[V, T]("either")

  object Either:
    def unapply[V, T](t: $[NonAbstractType[V, T]])(using SourcePos, LambdaContext): Some[$[T |*| T]] =
      Some(t.unpackedMatchAgainst(partition[V, T]["either"]))

  def recCall[V, T]: (T |*| T) -⚬ NonAbstractType[V, T] =
    pack ∘ inject[V, T]("recCall")

  object RecCall:
    def unapply[V, T](t: $[NonAbstractType[V, T]])(using SourcePos, LambdaContext): Some[$[T |*| T]] =
      Some(t.unpackedMatchAgainst(partition[V, T]["recCall"]))

  def fix[V, T]: Val[TypeConstructor.Fix[ScalaTypeParam, ?]] -⚬ NonAbstractType[V, T] =
    pack ∘ inject[V, T]("recType") ∘ OneOf.inject("fix")

  def pfixs[V, T]: (Val[TypeConstructor.PFix[ScalaTypeParam, ?, ?]] |*| Types[T]) -⚬ NonAbstractType[V, T] =
    pack ∘ inject[V, T]("recType") ∘ OneOf.inject("pfix")

  def pfix[V, T]: (Val[TypeConstructor.PFix[ScalaTypeParam, ●, ?]] |*| T) -⚬ NonAbstractType[V, T] =
    pfixs ∘ par(mapVal(p => p), Types.singleType[T])

  object RecType:
    def unapply[V, T](t: $[NonAbstractType[V, T]])(using SourcePos, LambdaContext): Some[$[FixOrPFix[T]]] =
      Some(t.unpackedMatchAgainst(partition[V, T]["recType"]))

  object Fix:
    def unapply[T](t: $[FixOrPFix[T]])(using SourcePos, LambdaContext): Some[$[Val[TypeConstructor.Fix[ScalaTypeParam, ?]]]] =
      Some(t.matchAgainst("fix"))

  object PFix:
    def unapply[T](t: $[FixOrPFix[T]])(using SourcePos, LambdaContext): Some[$[Val[TypeConstructor.PFix[ScalaTypeParam, ?, ?]] |*| Types[T]]] =
      Some(t.matchAgainst("pfix"))

  def string[V, T]: Done -⚬ NonAbstractType[V, T] =
    pack ∘ inject[V, T]("string")

  object String:
    def unapply[V, T](t: $[NonAbstractType[V, T]])(using SourcePos, LambdaContext): Some[$[Done]] =
      Some(t.unpackedMatchAgainst(partition[V, T]["string"]))

  def int[V, T]: Done -⚬ NonAbstractType[V, T] =
    pack ∘ inject[V, T]("int")

  object Int:
    def unapply[V, T](t: $[NonAbstractType[V, T]])(using SourcePos, LambdaContext): Some[$[Done]] =
      Some(t.unpackedMatchAgainst(partition[V, T]["int"]))

  def unit[V, T]: Done -⚬ NonAbstractType[V, T] =
    pack ∘ inject[V, T]("unit")

  object Unit:
    def unapply[V, T](t: $[NonAbstractType[V, T]])(using SourcePos, LambdaContext): Some[$[Done]] =
      Some(t.unpackedMatchAgainst(partition[V, T]["unit"]))

  def error[V, T]: TypeError[V, NonAbstractType[V, T]] -⚬ NonAbstractType[V, T] =
    pack ∘ inject[V, T]("error")

  def forbiddenSelfReference[V, T]: V -⚬ NonAbstractType[V, T] =
     error ∘ OneOf.inject("selfRef")

  def mismatch[V, T]: (NonAbstractType[V, T] |*| NonAbstractType[V, T]) -⚬ NonAbstractType[V, T] =
    error ∘ OneOf.inject("mismatch")

  object Error:
    def unapply[V, T](t: $[NonAbstractType[V, T]])(using SourcePos, LambdaContext): Some[$[TypeError[V, NonAbstractType[V, T]]]] =
      Some(t.unpackedMatchAgainst(partition[V, T]["error"]))

  object TypeMismatch:
    def unapply[V, T](e: $[TypeError[V, NonAbstractType[V, T]]])(using SourcePos, LambdaContext): Some[$[NonAbstractType[V, T] |*| NonAbstractType[V, T]]] =
      Some(e.matchAgainst("mismatch"))

  object ForbiddenSelfRef:
    def unapply[V, T](e: $[TypeError[V, NonAbstractType[V, T]]])(using SourcePos, LambdaContext): Some[$[V]] =
      Some(e.matchAgainst("selfRef"))

  def lift[V, T](
    inject: NonAbstractType[V, T] -⚬ T,
    absType: Label => (One -⚬ T),
    t: Type[ScalaTypeParam],
  ): One -⚬ T = {
    import libretto.typology.toylang.types.{TypeConstructor => TC}

    val ct = new CompilationTarget[V, T](inject, absType)
    import ct.{Map_○, Map_●}

    t.compile[-⚬, |*|, One, ct.as, One](
      Map_○,
      ct.compilePrimitive,
    )(using coreLib.category)
      .get(Map_○, Map_●)
  }

  def isPair[V, T]: NonAbstractType[V, T] -⚬ (NonAbstractType[V, T] |+| (T |*| T)) =
    λ { t =>
      switch(t)
        .is { case Pair(r |*| s) => injectR(r |*| s) }
        .is { case other         => injectL(other) }
        .end
    }

  def isRecCall[V, T]: NonAbstractType[V, T] -⚬ (NonAbstractType[V, T] |+| (T |*| T)) =
    λ { t =>
      switch(t)
        .is { case RecCall(r |*| s) => injectR(r |*| s) }
        .is { case other            => injectL(other) }
        .end
    }

  def map[V, T, U](g: T -⚬ U): NonAbstractType[V, T] -⚬ NonAbstractType[V, U] = rec { self =>
    λ { t =>
      switch(t)
        .is { case Pair(r |*| s) => pair(g(r) |*| g(s)) }
        .is { case Either(r |*| s) => either(g(r) |*| g(s)) }
        .is { case RecCall(r |*| s) => recCall(g(r) |*| g(s)) }
        .is { case RecType(Fix(f)) => fix(f) }
        .is { case RecType(PFix(f |*| x)) => pfixs(f |*| Types.map(g)(x)) }
        .is { case String(d) => string(d) }
        .is { case Int(d) => int(d) }
        .is { case Unit(d) => unit(d) }
        .is { case Error(TypeMismatch(x |*| y)) => mismatch(self(x) |*| self(y)) }
        .is { case Error(ForbiddenSelfRef(v)) => forbiddenSelfReference(v) }
        .end
    }
  }

  def mapWith[V, X, A, B](g: (X |*| A) -⚬ B)(using
    X: CloseableCosemigroup[X],
    V: Junction.Positive[V],
  ): (X |*| NonAbstractType[V, A]) -⚬ NonAbstractType[V, B] = rec { self =>
    λ { case +(x) |*| t =>
      switch(t)
        .is { case Pair(r |*| s) => pair(g(x |*| r) |*| g(x |*| s)) }
        .is { case Either(r |*| s) => either(g(x |*| r) |*| g(x |*| s)) }
        .is { case RecCall(r |*| s) => recCall(g(x |*| r) |*| g(x |*| s)) }
        .is { case RecType(Fix(f)) => fix(f waitFor X.close(x)) }
        .is { case RecType(PFix(f |*| ts)) => pfixs(f |*| Types.mapWith(g)(x |*| ts)) }
        .is { case String(d) => string(d waitFor X.close(x)) }
        .is { case Int(d) => int(d waitFor X.close(x)) }
        .is { case Unit(d) => unit(d waitFor X.close(x)) }
        .is { case Error(TypeMismatch(y |*| z)) => mismatch(self(x |*| y) |*| self(x |*| z)) }
        .is { case Error(ForbiddenSelfRef(v)) => forbiddenSelfReference(v waitFor X.close(x)) }
        .end
    }
  }

  def splitMap[V, T, Y, Z](
    f: T -⚬ (Y |*| Z),
  )(using
    Cosemigroup[V],
  ): NonAbstractType[V, T] -⚬ (NonAbstractType[V, Y] |*| NonAbstractType[V, Z]) = rec { self =>
    λ { t =>
      switch(t)
        .is { case Pair(r |*| s) =>
          val r1 |*| r2 = f(r)
          val s1 |*| s2 = f(s)
          pair(r1 |*| s1) |*| pair(r2 |*| s2)
        }
        .is { case Either(r |*| s) =>
          val r1 |*| r2 = f(r)
          val s1 |*| s2 = f(s)
          either(r1 |*| s1) |*| either(r2 |*| s2)
        }
        .is { case RecCall(r |*| s) =>
          val r1 |*| r2 = f(r)
          val s1 |*| s2 = f(s)
          recCall(r1 |*| s1) |*| recCall(r2 |*| s2)
        }
        .is { case RecType(Fix(+(g))) => fix(g) |*| fix(g) }
        .is { case RecType(PFix(+(g) |*| t)) =>
          val t1 |*| t2 = Types.splitMap(f)(t)
          pfixs(g |*| t1) |*| pfixs(g |*| t2)
        }
        .is { case String(+(t)) => string(t) |*| string(t) }
        .is { case Int(+(t)) => int(t) |*| int(t) }
        .is { case Unit(+(t)) => unit(t) |*| unit(t) }
        .is { case Error(ForbiddenSelfRef(+(v))) =>
          forbiddenSelfReference(v) |*| forbiddenSelfReference(v)
        }
        .is { case Error(TypeMismatch(x1 |*| x2)) =>
          val y1 |*| z1 = self(x1)
          val y2 |*| z2 = self(x2)
          mismatch(y1 |*| y2) |*| mismatch(z1 |*| z2)
        }
        .end
    }
  }

  def split[V, T](
    splitElem: T -⚬ (T |*| T),
  )(using
    Cosemigroup[V],
  ): NonAbstractType[V, T] -⚬ (NonAbstractType[V, T] |*| NonAbstractType[V, T]) =
    splitMap(splitElem)

  def merge[V, T](
    g: (T |*| T) -⚬ T,
  ): (NonAbstractType[V, T] |*| NonAbstractType[V, T]) -⚬ NonAbstractType[V, T] = {
    λ { case a |*| b =>
      switch(a |*| b)
        .is { case Pair(a1 |*| a2) |*| Pair(b1 |*| b2) => pair(g(a1 |*| b1) |*| g(a2 |*| b2)) }
        .is { case Either(p |*| q) |*| Either(r |*| s) => either(g(p |*| r) |*| g(q |*| s)) }
        .is { case RecCall(p |*| q) |*| RecCall(r |*| s) => recCall(g(p |*| r) |*| g(q |*| s)) }
        .is { case RecType(Fix(f)) |*| RecType(Fix(g)) =>
          ((f ** g) :>> mapVal { case (f, g) =>
            if (f == g) Left(f)
            else        Right((f, g))
          } :>> liftEither) either {
            case Left(f) =>
              fix(f)
            case Right(fg) =>
              mismatch(fg :>> liftPair :>> par(fix, fix))
          }
        }
        .is { case RecType(PFix(f |*| x)) |*| RecType(PFix(h |*| y)) =>
          ((f ** h) :>> mapVal { case (f, h) =>
            if (f == h) Left(f)
            else        Right((f, h))
          } :>> liftEither) either {
            case Left(f)   => pfixs(f |*| Types.merge(g)(x |*| y))
            case Right(fh) => (fh |*| x |*| y) :>> crashNow(s"TODO type mismatch (at ${summon[SourcePos]})")
          }
        }
        .is { case String(x) |*| String(y) => string(join(x |*| y)) }
        .is { case Int(x) |*| Int(y) => int(join(x |*| y)) }
        .is { case Unit(x) |*| Unit(y) => unit(join(x |*| y)) }
        .is { case Error(a) |*| Error(b) =>
          mismatch(error(a) |*| error(b)) // TODO: support multiple error accumulation instead
        }
        .is { case a |*| b => mismatch(a |*| b) }
        .end
    }
  }

  def output[V, T](
    outputElem: T -⚬ Val[Type[Label]],
    selfRef: V -⚬ Val[Type[Label]],
  ): NonAbstractType[V, T] -⚬ Val[Type[Label]] = rec { self =>
    λ { x =>
      switch(x)
        .is { case Pair(x1 |*| x2) =>
          (outputElem(x1) ** outputElem(x2)) :>> mapVal { case (t1, t2) =>
            Type.pair(t1, t2)
          }
        }
        .is { case Either(a |*| b) =>
          (outputElem(a) ** outputElem(b)) :>> mapVal { case (a, b) =>
            Type.pair(a, b)
          }
        }
        .is { case RecCall(a |*| b) =>
          (outputElem(a) ** outputElem(b)) :>> mapVal { case (a, b) =>
            Type.recCall(a, b)
          }
        }
        .is { case RecType(Fix(f)) =>
          f :>> mapVal { f => Type.fix(f.vmap(Label.ScalaTParam(_))) }
        }
        .is { case RecType(PFix(pf |*| p)) =>
          (pf ** Types.output(outputElem)(p)) :>> mapVal { case (pf, p) =>
            Type.Fun.pfixUnsafe(pf.vmap(Label.ScalaTParam(_)), p)
          }
        }
        .is { case String(x) => x :>> constVal(Type.string) }
        .is { case Int(x) => x :>> constVal(Type.int) }
        .is { case Unit(x) => x :>> constVal(Type.unit) }
        .is { case Error(ForbiddenSelfRef(v)) => selfRef(v) }
        .is { case Error(TypeMismatch(x |*| y)) =>
          (self(x) ** self(y)) :>> mapVal { case (t, u) => Type.typeMismatch(t, u) }
        }
        .end
    }
  }

  def close[V, T](
    closeElem: T -⚬ Done,
    closeVar: V -⚬ Done,
  ): NonAbstractType[V, T] -⚬ Done = rec { self =>
    λ { t =>
      switch(t)
        .is { case Pair(a |*| b) => join(closeElem(a) |*| closeElem(b)) }
        .is { case Either(a |*| b) => join(closeElem(a) |*| closeElem(b)) }
        .is { case RecCall(a |*| b) => join(closeElem(a) |*| closeElem(b)) }
        .is { case RecType(Fix(f)) => neglect(f) }
        .is { case RecType(PFix(f |*| x)) => join(neglect(f) |*| Types.close(closeElem)(x)) }
        .is { case String(x) => x }
        .is { case Int(x) => x }
        .is { case Unit(x) => x }
        .is { case Error(ForbiddenSelfRef(v)) => closeVar(v) }
        .is { case Error(TypeMismatch(x |*| y)) => join(self(x) |*| self(y)) }
        .end
    }
  }

  def awaitPosFst[V, T](
    g: (Done |*| T) -⚬ T,
    h: (Done |*| V) -⚬ V,
  ): (Done |*| NonAbstractType[V, T]) -⚬ NonAbstractType[V, T] = rec { self =>
    λ { case d |*| t =>
      switch(t)
        .is { case Pair(a |*| b) => pair(g(d |*| a) |*| b) }
        .is { case Either(a |*| b) => either(g(d |*| a) |*| b) }
        .is { case RecCall(a |*| b) => recCall(g(d |*| a) |*| b) }
        .is { case RecType(Fix(f)) => fix(f waitFor d) }
        .is { case RecType(PFix(f |*| x)) => pfixs(f.waitFor(d) |*| x) }
        .is { case String(x) => string(join(d |*| x)) }
        .is { case Int(x) => int(join(d |*| x)) }
        .is { case Unit(x) => unit(join(d |*| x)) }
        .is { case Error(ForbiddenSelfRef(v)) => forbiddenSelfReference(h(d |*| v)) }
        .is { case Error(TypeMismatch(x |*| y)) => mismatch(self(d |*| x) |*| y) }
        .end
    }
  }

  given junctionNonAbstractType[V, T](using
    T: Junction.Positive[T],
    V: Junction.Positive[V],
  ): Junction.Positive[NonAbstractType[V, T]] with {
    override def awaitPosFst: (Done |*| NonAbstractType[V, T]) -⚬ NonAbstractType[V, T] =
      NonAbstractType.awaitPosFst[V, T](T.awaitPosFst, V.awaitPosFst)
  }

  private class CompilationTarget[V, T](
    lift: NonAbstractType[V, T] -⚬ T,
    absType: Label => (One -⚬ T),
  ) {
    def toTypes[P, Q](pq: P as Q)(using p: KindN[P]): Q -⚬ Types[T] =
      pq match
        case Map_○ =>
          KindN.cannotBeUnit(p)
        case Map_● =>
          Types.singleType[T]
        case π: Pair[p1, p2, q1, q2] =>
          val (p1, p2) = KindN.unpair(p: KindN[p1 × p2])
          par(
            toTypes(π.f1)(using p1),
            toTypes(π.f2)(using p2),
          ) > Types.prod

    def compilePFix[P, Q, X](
      pq: P as Q,
      f: TypeConstructor.PFix[ScalaTypeParam, P, X],
    )(using
      KindN[P],
    ): Q -⚬ T =
      λ { q =>
        (constantVal(f) |*| toTypes(pq)(q)) :>> NonAbstractType.pfixs :>> lift
      }

    def doCompilePrimitive[k, l, q](
      fk: k as q,
      x: TypeConstructor[ScalaTypeParam, k, l],
    ): MappedMorphism[-⚬, as, k, l] = {
      import TypeConstructor.{Pair as _, *}
      x match {
        case UnitType() =>
          MappedMorphism(Map_○, done > NonAbstractType.unit > lift, Map_●)
        case IntType() =>
          MappedMorphism(Map_○, done > NonAbstractType.int > lift, Map_●)
        case StringType() =>
          MappedMorphism(Map_○, done > NonAbstractType.string > lift, Map_●)
        case TypeConstructor.Pair() =>
          MappedMorphism(Pair(Map_●, Map_●), NonAbstractType.pair > lift, Map_●)
        case Sum() =>
          MappedMorphism(Pair(Map_●, Map_●), NonAbstractType.either > lift, Map_●)
        case TypeConstructor.RecCall() =>
          MappedMorphism(Pair(Map_●, Map_●), NonAbstractType.recCall > lift, Map_●)
        case f @ TypeConstructor.Fix(_, _) =>
          MappedMorphism(Map_○, const(f) > NonAbstractType.fix > lift, Map_●)
        case p @ TypeConstructor.PFix(_, _) =>
          import p.g.inKind1
          MappedMorphism(fk, compilePFix(fk, p), Map_●)
        case AbstractType(label) =>
          MappedMorphism(Map_○, absType(Label.ScalaTParam(label)), Map_●)
        case TypeConstructor.TypeMismatch(a, b) =>
          UnhandledCase.raise(s"TypeMismatch($a, $b)")
        case TypeConstructor.ForbiddenSelfRef(v) =>
          UnhandledCase.raise(s"ForbiddenSelfReference($v)")
      }
    }

    val compilePrimitive: [k, l, q] => (
      k as q,
      TypeConstructor[ScalaTypeParam, k, l],
    ) => MappedMorphism[-⚬, as, k, l] =
      [k, l, q] => (
        fk: k as q,
        x: TypeConstructor[ScalaTypeParam, k, l],
      ) =>
        doCompilePrimitive[k, l, q](fk, x)

    infix sealed trait as[K, Q]

    case object Map_○ extends as[○, One]
    case object Map_● extends as[●, T]
    case class Pair[K1, K2, Q1, Q2](
      f1: K1 as Q1,
      f2: K2 as Q2,
    ) extends as[K1 × K2, Q1 |*| Q2]

    def split[K, Q](splitT: T -⚬ (T |*| T))(
      kq: K as Q,
    ): Q -⚬ (Q |*| Q) =
      kq match {
        case Map_● =>
          splitT
        case other =>
          UnhandledCase.raise(s"split($other)")
      }

    given objectMap: MonoidalObjectMap[as, ×, ○, |*|, One] =
      new MonoidalObjectMap[as, ×, ○, |*|, One] {

        override def uniqueOutputType[A, B, C](f: as[A, B], g: as[A, C]): B =:= C =
          (f, g) match {
            case (Map_○, Map_○) => summon[B =:= C]
            case (Map_●, Map_●) => summon[B =:= C]
            case (Pair(f1, f2), Pair(g1, g2)) =>
              (uniqueOutputType(f1, g1), uniqueOutputType(f2, g2)) match {
                case (TypeEq(Refl()), TypeEq(Refl())) =>
                  summon[B =:= C]
              }
          }

        override def pair[A1, A2, X1, X2](f1: as[A1, X1], f2: as[A2, X2]): as[A1 × A2, X1 |*| X2] =
          Pair(f1, f2)

        override def unpair[A1, A2, X](f: as[A1 × A2, X]): Unpaired[A1, A2, X] =
          f match {
            case Pair(f1, f2) => Unpaired.Impl(f1, f2)
          }

        override def unit: as[○, One] =
          Map_○
      }
  }

  given TypeOps[NonAbstractType[Val[Label], _], Type[Label], Label] with {
    override def map[A, B](f: A -⚬ B): NonAbstractType[Val[Label], A] -⚬ NonAbstractType[Val[Label], B] =
      NonAbstractType.map(f)

    override def mapWith[X, A, B](
      f: (X |*| A) -⚬ B,
    )(using CloseableCosemigroup[X]): (X |*| NonAbstractType[Val[Label], A]) -⚬ NonAbstractType[Val[Label], B] =
      NonAbstractType.mapWith(f)

    override def merge[A](
      f: (A |*| A) -⚬ A,
    ): (NonAbstractType[Val[Label], A] |*| NonAbstractType[Val[Label], A]) -⚬ NonAbstractType[Val[Label], A] =
      NonAbstractType.merge(f)

    override def split[A](f: A -⚬ (A |*| A)): NonAbstractType[Val[Label], A] -⚬ (NonAbstractType[Val[Label], A] |*| NonAbstractType[Val[Label], A]) =
      NonAbstractType.split(f)

    override def output[A](f: A -⚬ Val[Type[Label]]): NonAbstractType[Val[Label], A] -⚬ Val[Type[Label]] =
      NonAbstractType.output(f, mapVal(Type.forbiddenSelfReference(_)))

    override def close[A](f: A -⚬ Done): NonAbstractType[Val[Label], A] -⚬ Done =
      NonAbstractType.close(f, neglect)

    override def forbiddenSelfReference[A]: Val[Label] -⚬ NonAbstractType[Val[Label], A] =
      NonAbstractType.forbiddenSelfReference

    override def awaitPosFst[A](f: (Done |*| A) -⚬ A): (Done |*| NonAbstractType[Val[Label], A]) -⚬ NonAbstractType[Val[Label], A] =
      NonAbstractType.awaitPosFst(f, summon[Junction.Positive[Val[Label]]].awaitPosFst)
  }
}
