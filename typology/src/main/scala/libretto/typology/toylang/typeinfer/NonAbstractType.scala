package libretto.typology.toylang.typeinfer

import libretto.lambda.{Extractor, MappedMorphism, MonoidalObjectMap, SymmetricMonoidalCategory, UnhandledCase}
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
  def SingleType[T]: Extractor[-⚬, |*|, Types[T],T] =
    OneOf.partition[TypesF[T, Types[T]]]["singleType"].afterUnpack

  def Prod[T]: Extractor[-⚬, |*|, Types[T], Types[T] |*| Types[T]] =
    OneOf.partition[TypesF[T, Types[T]]]["prod"].afterUnpack

  def KindMismatch[T]: Extractor[-⚬, |*|, Types[T], KindMismatch[Types[T]]] =
    OneOf.partition[TypesF[T, Types[T]]]["kindMismatch"].afterUnpack

  def map[T, U](f: T -⚬ U): Types[T] -⚬ Types[U] =
    rec { self =>
      λ { ts =>
        switch(ts)
          .is { case KindMismatch(x |*| y) => KindMismatch(self(x) |*| self(y)) }
          .is { case SingleType(t) => SingleType(f(t)) }
          .is { case Prod(ts1 |*| ts2) => Prod(self(ts1) |*| self(ts2)) }
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
            KindMismatch(xu |*| yu) |*| KindMismatch(xv |*| yv)
          }
          .is { case SingleType(t) =>
            val u |*| v = f(t)
            SingleType(u) |*| SingleType(v)
          }
          .is { case Prod(ts1 |*| ts2) =>
            val (u1 |*| v1) = self(ts1)
            val (u2 |*| v2) = self(ts2)
            Prod(u1 |*| u2) |*| Prod(v1 |*| v2)
          }
          .end
      }
    }

  def mapWith[X, T, U](f: (X |*| T) -⚬ U)(using Cosemigroup[X]): (X |*| Types[T]) -⚬ Types[U] =
    rec { self =>
      λ { case +(x) |*| ts =>
        switch(ts)
          .is { case KindMismatch(p |*| q) => KindMismatch(self(x |*| p) |*| self(x |*| q)) }
          .is { case SingleType(t) => SingleType(f(x |*| t)) }
          .is { case Prod(ts1 |*| ts2) => Prod(self(x |*| ts1) |*| self(x |*| ts2)) }
          .end
      }
    }

  def merge[T](f: (T |*| T) -⚬ T): (Types[T] |*| Types[T]) -⚬ Types[T] =
    rec { self =>
      λ { case ts |*| us =>
        switch(ts |*| us)
          .is { case SingleType(t) |*| SingleType(u) => SingleType(f(t |*| u)) }
          .is { case Prod(t1 |*| t2) |*| Prod(u1 |*| u2) => Prod(self(t1 |*| u1) |*| self(t2 |*| u2)) }
          .is { case ts |*| us => KindMismatch(ts |*| us) }
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

  def Pair[V, T]: Extractor[-⚬, |*|, NonAbstractType[V, T], T |*| T] =
    partition[V, T]["pair"].afterUnpack

  def Either[V, T]: Extractor[-⚬, |*|, NonAbstractType[V, T], T |*| T] =
    partition[V, T]["either"].afterUnpack

  def RecCall[V, T]: Extractor[-⚬, |*|, NonAbstractType[V, T], T |*| T] =
    partition[V, T]["recCall"].afterUnpack

  def fix[V, T]: Val[TypeConstructor.Fix[ScalaTypeParam, ?]] -⚬ NonAbstractType[V, T] =
    RecType.reinject ∘ Fix.reinject

  def pfixs[V, T]: (Val[TypeConstructor.PFix[ScalaTypeParam, ?, ?]] |*| Types[T]) -⚬ NonAbstractType[V, T] =
    RecType.reinject ∘ PFix.reinject

  def pfix[V, T]: (Val[TypeConstructor.PFix[ScalaTypeParam, ●, ?]] |*| T) -⚬ NonAbstractType[V, T] =
    pfixs ∘ par(mapVal(p => p), Types.SingleType[T].reinject)

  def RecType[V, T]: Extractor[-⚬, |*|, NonAbstractType[V, T], FixOrPFix[T]] =
    partition[V, T]["recType"].afterUnpack

  def Fix[T]: Extractor[-⚬, |*|, FixOrPFix[T], Val[TypeConstructor.Fix[ScalaTypeParam, ?]]] =
    OneOf.partition[FixOrPFix[T]]["fix"]

  def PFix[T]: Extractor[-⚬, |*|, FixOrPFix[T], Val[TypeConstructor.PFix[ScalaTypeParam, ?, ?]] |*| Types[T]] =
    OneOf.partition[FixOrPFix[T]]["pfix"]

  def String[V, T]: Extractor[-⚬, |*|, NonAbstractType[V, T], Done] =
    partition[V, T]["string"].afterUnpack

  def Int[V, T]: Extractor[-⚬, |*|, NonAbstractType[V, T], Done] =
    partition[V, T]["int"].afterUnpack

  def Unit[V, T]: Extractor[-⚬, |*|, NonAbstractType[V, T], Done] =
    partition[V, T]["unit"].afterUnpack

  def forbiddenSelfReference[V, T]: V -⚬ NonAbstractType[V, T] =
     Error.reinject ∘ ForbiddenSelfRef.reinject

  def mismatch[V, T]: (NonAbstractType[V, T] |*| NonAbstractType[V, T]) -⚬ NonAbstractType[V, T] =
    Error.reinject ∘ TypeMismatch.reinject

  def Error[V, T]: Extractor[-⚬, |*|, NonAbstractType[V, T], TypeError[V, NonAbstractType[V, T]]] =
    partition[V, T]["error"].afterUnpack

  def TypeMismatch[V, T]: Extractor[-⚬, |*|, TypeError[V, NonAbstractType[V, T]], NonAbstractType[V, T] |*| NonAbstractType[V, T]] =
    OneOf.partition[TypeError[V, NonAbstractType[V, T]]]["mismatch"]

  def ForbiddenSelfRef[V, T]: Extractor[-⚬, |*|, TypeError[V, NonAbstractType[V, T]], V] =
    OneOf.partition[TypeError[V, NonAbstractType[V, T]]]["selfRef"]

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
        .is { case Pair(r |*| s) => Pair(g(r) |*| g(s)) }
        .is { case Either(r |*| s) => Either(g(r) |*| g(s)) }
        .is { case RecCall(r |*| s) => RecCall(g(r) |*| g(s)) }
        .is { case RecType(Fix(f)) => fix(f) }
        .is { case RecType(PFix(f |*| x)) => pfixs(f |*| Types.map(g)(x)) }
        .is { case String(d) => String(d) }
        .is { case Int(d) => Int(d) }
        .is { case Unit(d) => Unit(d) }
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
        .is { case Pair(r |*| s) => Pair(g(x |*| r) |*| g(x |*| s)) }
        .is { case Either(r |*| s) => Either(g(x |*| r) |*| g(x |*| s)) }
        .is { case RecCall(r |*| s) => RecCall(g(x |*| r) |*| g(x |*| s)) }
        .is { case RecType(Fix(f)) => fix(f waitFor X.close(x)) }
        .is { case RecType(PFix(f |*| ts)) => pfixs(f |*| Types.mapWith(g)(x |*| ts)) }
        .is { case String(d) => String(d waitFor X.close(x)) }
        .is { case Int(d) => Int(d waitFor X.close(x)) }
        .is { case Unit(d) => Unit(d waitFor X.close(x)) }
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
          Pair(r1 |*| s1) |*| Pair(r2 |*| s2)
        }
        .is { case Either(r |*| s) =>
          val r1 |*| r2 = f(r)
          val s1 |*| s2 = f(s)
          Either(r1 |*| s1) |*| Either(r2 |*| s2)
        }
        .is { case RecCall(r |*| s) =>
          val r1 |*| r2 = f(r)
          val s1 |*| s2 = f(s)
          RecCall(r1 |*| s1) |*| RecCall(r2 |*| s2)
        }
        .is { case RecType(Fix(+(g))) => fix(g) |*| fix(g) }
        .is { case RecType(PFix(+(g) |*| t)) =>
          val t1 |*| t2 = Types.splitMap(f)(t)
          pfixs(g |*| t1) |*| pfixs(g |*| t2)
        }
        .is { case String(+(t)) => String(t) |*| String(t) }
        .is { case Int(+(t)) => Int(t) |*| Int(t) }
        .is { case Unit(+(t)) => Unit(t) |*| Unit(t) }
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
        .is { case Pair(a1 |*| a2) |*| Pair(b1 |*| b2) => Pair(g(a1 |*| b1) |*| g(a2 |*| b2)) }
        .is { case Either(p |*| q) |*| Either(r |*| s) => Either(g(p |*| r) |*| g(q |*| s)) }
        .is { case RecCall(p |*| q) |*| RecCall(r |*| s) => RecCall(g(p |*| r) |*| g(q |*| s)) }
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
        .is { case String(x) |*| String(y) => String(join(x |*| y)) }
        .is { case Int(x) |*| Int(y) => Int(join(x |*| y)) }
        .is { case Unit(x) |*| Unit(y) => Unit(join(x |*| y)) }
        .is { case Error(a) |*| Error(b) =>
          mismatch(Error(a) |*| Error(b)) // TODO: support multiple error accumulation instead
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
        .is { case Pair(a |*| b) => Pair(g(d |*| a) |*| b) }
        .is { case Either(a |*| b) => Either(g(d |*| a) |*| b) }
        .is { case RecCall(a |*| b) => RecCall(g(d |*| a) |*| b) }
        .is { case RecType(Fix(f)) => fix(f waitFor d) }
        .is { case RecType(PFix(f |*| x)) => pfixs(f.waitFor(d) |*| x) }
        .is { case String(x) => String(join(d |*| x)) }
        .is { case Int(x) => Int(join(d |*| x)) }
        .is { case Unit(x) => Unit(join(d |*| x)) }
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
          Types.SingleType[T].reinject
        case π: Pair[p1, p2, q1, q2] =>
          val (p1, p2) = KindN.unpair(p: KindN[p1 × p2])
          par(
            toTypes(π.f1)(using p1),
            toTypes(π.f2)(using p2),
          ) > Types.Prod.reinject

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
          MappedMorphism(Map_○, done > Unit.reinject > lift, Map_●)
        case IntType() =>
          MappedMorphism(Map_○, done > Int.reinject > lift, Map_●)
        case StringType() =>
          MappedMorphism(Map_○, done > String.reinject > lift, Map_●)
        case TypeConstructor.Pair() =>
          MappedMorphism(Pair(Map_●, Map_●), NonAbstractType.Pair.reinject > lift, Map_●)
        case Sum() =>
          MappedMorphism(Pair(Map_●, Map_●), Either.reinject > lift, Map_●)
        case TypeConstructor.RecCall() =>
          MappedMorphism(Pair(Map_●, Map_●), NonAbstractType.RecCall.reinject > lift, Map_●)
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
