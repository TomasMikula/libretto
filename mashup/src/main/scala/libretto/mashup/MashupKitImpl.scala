package libretto.mashup

import libretto.{Executor, StarterKit, scalasource}
import scala.concurrent.Future
import java.util.concurrent.ScheduledExecutorService

object MashupKitImpl extends MashupKit { kit =>
  import StarterKit.dsl.{-⚬, =⚬, |*|, |+|, One, Val}
  import StarterKit.dsl.$.>

  override object dsl extends MashupDsl {
    override type Fun[A, B] = A -⚬ B // for now, let's just use libretto's linear functions

    override type EmptyResource = One

    override type or[A, B] = A |+| B

    override type -->[A, B] = A =⚬ B

    override type Text = Val[String]

    override type Float64 = Val[Double]

    override type Expr[A] = StarterKit.dsl.$[A]

    override type Record = One

    override type ##[A, B] = A |*| B

    override type of[Name <: String, T] = T

    override def fun[A, B](f: Expr[A] => Expr[B]): Fun[A, B] =
      StarterKit.dsl.λ(f)

    override def closure[A, B](f: Expr[A] => Expr[B]): Expr[A --> B] =
      StarterKit.dsl.Λ(f)

    override def id[A]: Fun[A, A] =
      StarterKit.dsl.id[A]

    override def left[A, B]: Fun[A, A or B] =
      StarterKit.dsl.injectL[A, B]

    override def right[A, B]: Fun[B, A or B] =
      StarterKit.dsl.injectR[A, B]

    override object Record extends Records {
      override def apply()(using pos: scalasource.Position): Expr[Record] =
        StarterKit.dsl.$.one(using pos)
    }

    override object Float64 extends Float64s {
      override def apply(value: Double)(using pos: scalasource.Position): Expr[Float64] =
        StarterKit.dsl.$.one(using pos) > StarterKit.dsl.done > StarterKit.dsl.constVal(value)
    }

    override object Expr extends Exprs {
      override def eliminateSecond[A](a: Expr[A], empty: Expr[EmptyResource])(pos: scalasource.Position): Expr[A] =
        StarterKit.dsl.$.eliminateSecond(a, empty)(pos)

      override def extendRecord[A, N <: String, T](init: Expr[A], last: (N, Expr[T]))(pos: scalasource.Position): Expr[A ## (N of T)] =
        StarterKit.dsl.$.zip(init, last._2)(pos)
    }
  }

  override def createRuntime(executor: ScheduledExecutorService): MashupRuntime[dsl.type] = {
    val exec = StarterKit.executor(executor)(executor)
    new RuntimeImpl(exec)
  }

  private class RuntimeImpl(
    executor: Executor.Of[StarterKit.dsl.type, Future],
  ) extends MashupRuntime[dsl.type] {
      override val dsl: kit.dsl.type = kit.dsl

      override opaque type InPort[A]  = executor.InPort[A]
      override opaque type OutPort[A] = executor.OutPort[A]
      override opaque type Execution  = executor.Execution

      override def run[A, B](prg: dsl.Fun[A, B]): (InPort[A], OutPort[B], Execution) =
        executor.execute(prg)
  }
}
