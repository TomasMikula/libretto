package libretto.mashup

import libretto.{ScalaExecutor, StarterKit, scalasource}
import libretto.util.Async
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success, Try}
import java.util.concurrent.ScheduledExecutorService

object MashupKitImpl extends MashupKit { kit =>
  import StarterKit.dsl.{-⚬, =⚬, |*|, |+|, Done, One, Val, chooseL, chooseR, liftPair, mapVal, par, unliftPair}
  import StarterKit.dsl.$.>
  import StarterKit.coreLib.Junction

  override object dsl extends MashupDsl {
    override type Fun[A, B] = A -⚬ B // for now, let's just use libretto's linear functions

    override type EmptyResource = One

    // TODO: later distinguish between product on *data* types and monoidal product on resources
    override type **[A, B] = A |*| B

    override type or[A, B] = A |+| B

    override type -->[A, B] = A =⚬ B

    override type Text = Val[String]

    override type Float64 = Val[Double]

    override type Expr[A] = StarterKit.dsl.$[A]

    override type Record[A] = A

    override type ###[A, B] = A |*| B

    override type of[Name <: String, T] = T

    override type |&|[A, B] = StarterKit.dsl.|&|[A, B]

    override type ValueType[A] = ValueTypeImpl[A]

    override type Unlimited[A] = StarterKit.coreLib.Unlimited[A]

    override type Pick[A, K <: String & Singleton] = AbstractPick[A, K]

    override def fun[A, B](f: Expr[A] => Expr[B])(using pos: scalasource.Position): Fun[A, B] =
      StarterKit.dsl.λ(f)(using pos)

    override def closure[A, B](f: Expr[A] => Expr[B])(using pos: scalasource.Position): Expr[A --> B] =
      StarterKit.dsl.Λ(f)(using pos)

    override def id[A]: Fun[A, A] =
      StarterKit.dsl.id[A]

    override def left[A, B]: Fun[A, A or B] =
      StarterKit.dsl.injectL[A, B]

    override def right[A, B]: Fun[B, A or B] =
      StarterKit.dsl.injectR[A, B]

    override def eval[A, B]: Fun[(A --> B) ** A, B] =
      StarterKit.dsl.eval[A, B]

    override object Record extends Records {
      override def empty(using pos: scalasource.Position): Expr[Record[EmptyResource]] =
        StarterKit.dsl.$.one(using pos)

      override def field[N <: String & Singleton, T](field: (N, Expr[T])): Expr[Record[N of T]] =
        field._2
    }

    override object Text extends Texts {
      def apply(value: String)(using pos: scalasource.Position): Expr[Text] =
        StarterKit.dsl.$.one(using pos) > StarterKit.dsl.done > StarterKit.dsl.constVal(value)
    }

    override object Float64 extends Float64s {
      import StarterKit.dsl.$.{map, zip}

      override def apply(value: Double)(using pos: scalasource.Position): Expr[Float64] =
        StarterKit.dsl.$.one(using pos) > StarterKit.dsl.done > StarterKit.dsl.constVal(value)

      override def add(a: Expr[Float64], b: Expr[Float64])(using
        pos: scalasource.Position,
      ): Expr[Float64] =
        map(zip(a, b)(pos))(unliftPair > mapVal { case (a, b) => a + b })(pos)

      override def subtract(a: Expr[Float64], b: Expr[Float64])(using
        pos: scalasource.Position,
      ): Expr[Float64] =
        map(zip(a, b)(pos))(unliftPair > mapVal { case (a, b) => a - b })(pos)

      override def negate(a: Expr[Float64])(using
        pos: scalasource.Position,
      ): Expr[Float64] =
        map(a)(mapVal(a => -a))(pos)

      override def multiply(a: Expr[Float64], b: Expr[Float64])(using
        pos: scalasource.Position,
      ): Expr[Float64] =
        map(zip(a, b)(pos))(unliftPair > mapVal { case (a, b) => a * b })(pos)

      override def divide(a: Expr[Float64], b: Expr[Float64])(using
        pos: scalasource.Position,
      ): Expr[Float64] =
        map(zip(a, b)(pos))(unliftPair > mapVal { case (a, b) => a / b })(pos)
    }

    override object Expr extends Exprs {
      override def unit(using pos: scalasource.Position): Expr[EmptyResource] =
        StarterKit.dsl.$.one(using pos)

      override def pair[A, B](a: Expr[A], b: Expr[B])(using
        pos: scalasource.Position,
      ): Expr[A ** B] =
        StarterKit.dsl.$.zip(a, b)(pos)

      override def eliminateSecond[A](a: Expr[A], empty: Expr[EmptyResource])(pos: scalasource.Position): Expr[A] =
        StarterKit.dsl.$.eliminateSecond(a, empty)(pos)

      override def awaitSecond[A, B](a: Expr[A], b: Expr[B])(pos: scalasource.Position)(using
        A: ValueType[A],
        B: ValueType[B],
      ): Expr[A] = {
        import A.junction
        import StarterKit.dsl.$
        import StarterKit.coreLib.awaitPosSnd
        $.map($.zip(a, B.neglect(b)(using pos))(pos))(awaitPosSnd)(pos)
      }

      override def extendRecord[A, N <: String, T](init: Expr[A], last: (N, Expr[T]))(pos: scalasource.Position): Expr[A ### (N of T)] =
        StarterKit.dsl.$.zip(init, last._2)(pos)

      override def map[A, B](a: Expr[A], f: Fun[A, B])(using pos: scalasource.Position): Expr[B] =
        StarterKit.dsl.$.map(a)(f)(pos)

      override def debugPrint[A](s: String, expr: Expr[A])(using A: ValueType[A]): Expr[A] =
        expr >
          A.toScalaValue >
          StarterKit.scalaLib.alsoPrintLine(v => s"$s: $v") >
          A.fromScalaValue
    }

    override object Unlimited extends Unlimiteds {
      export StarterKit.coreLib.Unlimited.{discard, duplicate, map, single => getSingle, split}
    }

    override object ** extends PairExtractor {
      override def unapply[A, B](ab: Expr[A ** B])(using pos: scalasource.Position): (Expr[A], Expr[B]) =
        StarterKit.dsl.$.unzip(ab)(pos)
    }

    override object as extends SingleFieldExtractor {
      override def unapply[N <: String & Singleton, T](
        field: Expr[Record[N of T]],
      )(using
        N: ConstValue[N],
      ): (N, Expr[T]) =
        (N.value, field)
    }

    override object ### extends RecordExtractor {
      override def unapply[A, B](rec: Expr[Record[A ### B]])(using
        pos: scalasource.Position,
      ): (Expr[Record[A]], Expr[Record[B]]) =
        StarterKit.dsl.$.unzip(rec)(pos)
    }

    override def singleOptionPick[K <: String & Singleton, V]: Picked[K of V, K, V] =
      PickImpl(id[V])

    override def choicePickLeft[A, K <: String & Singleton, V, B](using
      ev: Picked[A, K, V],
    ): Picked[A |&| B, K, V] =
      PickImpl(chooseL > ev.asFun)

    override def choicePickRight[A, B, K <: String & Singleton, V](using
      ev: Picked[B, K, V],
    ): Picked[A |&| B, K, V] =
      PickImpl(chooseR > ev.asFun)

    private class PickImpl[A, K <: String & Singleton, V](f: Fun[A, V]) extends AbstractPick[A, K] {
      override type T = V

      override def asFun: Fun[A, V] = f
    }

    sealed trait ValueTypeImpl[A] {
      type ScalaRepr

      def toScalaValue: Fun[A, Val[ScalaRepr]]

      def fromScalaValue: Fun[Val[ScalaRepr], A]

      def readFrom(using rt: MashupRuntime[dsl.type], exn: rt.Execution)(
        port: exn.OutPort[A],
      ): Async[Try[rt.Value[A]]]

      given junction: Junction.Positive[A]

      def neglect: Fun[A, Done] =
        toScalaValue > StarterKit.dsl.neglect
    }

    override def valueTypeFloat64: ValueType[Float64] =
      new ValueTypeImpl[Float64] {
        override type ScalaRepr = Double

        override def junction: Junction.Positive[Float64] = StarterKit.scalaLib.junctionVal[Double]

        override def toScalaValue: Fun[Float64, Val[Double]] = id[Val[Double]]

        override def fromScalaValue: Fun[Val[Double], Float64] = id[Val[Double]]

        override def readFrom(using rt: MashupRuntime[dsl.type], exn: rt.Execution)(
          port: exn.OutPort[Float64],
        ): Async[Try[rt.Value[Float64]]] =
          exn.OutPort.float64Get(port)
            .map(_.map(rt.Value.float64(_)))
      }

    override def valueTypeText: ValueType[Text] =
      new ValueTypeImpl[Text] {
        override type ScalaRepr = String

        override def junction: Junction.Positive[Text] = StarterKit.scalaLib.junctionVal[String]

        override def toScalaValue: Fun[Text, Val[String]] = id[Val[String]]

        override def fromScalaValue: Fun[Val[String], Text] = id[Val[String]]

        override def readFrom(using rt: MashupRuntime[dsl.type], exn: rt.Execution)(
          port: exn.OutPort[Text],
        ): Async[Try[rt.Value[Text]]] =
          exn.OutPort.textGet(port)
            .map(_.map(rt.Value.text(_)))
      }

    override def valueTypeSingleFieldRecord[N <: String & Singleton, T](using
      N: ConstValue[N],
      T: ValueType[T],
    ): ValueType[Record[N of T]] =
      new ValueType[Record[N of T]] {
        override type ScalaRepr = (N, T.ScalaRepr)

        override def junction: Junction.Positive[Record[N of T]] = T.junction

        override def toScalaValue: Fun[Record[N of T], Val[ScalaRepr]] =
          T.toScalaValue > mapVal((N.value, _))

        override def fromScalaValue: Fun[Val[ScalaRepr], Record[N of T]] =
          mapVal[(N, T.ScalaRepr), T.ScalaRepr](_._2) > T.fromScalaValue

        override def readFrom(using rt: MashupRuntime[dsl.type], exn: rt.Execution)(
          port: exn.OutPort[Record[N of T]],
        ): Async[Try[rt.Value[N of T]]] =
          T.readFrom(exn.OutPort.recordGetSingle(port))
            .map(_.map(rt.Value.record(N.value, _)))
      }

    override def valueTypeRecord[A, N <: String & Singleton, T](using
      A: ValueType[A],
      N: ConstValue[N],
      T: ValueType[T],
    ): ValueType[Record[A ### (N of T)]] =
      new ValueType[Record[A ### (N of T)]] {
        override type ScalaRepr = (A.ScalaRepr, (N, T.ScalaRepr))

        override def junction: Junction.Positive[Record[A ### (N of T)]] =
          Junction.Positive.both(A.junction, T.junction)

        override def toScalaValue: Fun[Record[A ### (N of T)], Val[ScalaRepr]] =
          par(A.toScalaValue, T.toScalaValue) > unliftPair > mapVal { case (a, t) => (a, (N.value, t)) }

        override def fromScalaValue: Fun[Val[(A.ScalaRepr, (N, T.ScalaRepr))], Record[A |*| of[N, T]]] =
          liftPair > par(
            A.fromScalaValue,
            mapVal[(N, T.ScalaRepr), T.ScalaRepr](_._2) > T.fromScalaValue,
          )

        override def readFrom(using rt: MashupRuntime[dsl.type], exn: rt.Execution)(
          port: exn.OutPort[Record[A ### (N of T)]],
        ): Async[Try[rt.Value[Record[A ### (N of T)]]]] = {
          val (pa, pt) = exn.OutPort.split(port)
          for {
            a <- A.readFrom(pa)
            t <- T.readFrom(pt)
          } yield {
            for {
              a <- a
              t <- t
            } yield rt.Value.extendRecord(a, N.value, t)
          }
        }
      }
  }

  override def createRuntime(executor: ScheduledExecutorService): MashupRuntime[dsl.type] = {
    val exec = StarterKit.executor(executor)(executor)
    new RuntimeImpl(exec)
  }

  private class RuntimeImpl(
    executor: ScalaExecutor.Of[StarterKit.dsl.type],
  ) extends MashupRuntime[dsl.type] {
    override val dsl: kit.dsl.type = kit.dsl
    import dsl.{-->, **, ###, |&|, EmptyResource, Float64, Fun, Record, Text, Unlimited, ValueType, of}

    override opaque type Execution <: MashupExecution = ExecutionImpl[? <: executor.Execution]

    override def run[A, B](prg: dsl.Fun[A, B]): Executing[A, B] = {
      val executing = executor.execute(prg)
      type EXN = executing.execution.type
      val execution: EXN = executing.execution
      new Executing(new ExecutionImpl[EXN](execution), executing.inPort, executing.outPort)
    }

    sealed trait Value[A]

    override object Value extends Values {
      case object Unit extends Value[EmptyResource]
      case class Pair[A, B](a: Value[A], b: Value[B]) extends Value[A ** B]
      case class Txt(value: String) extends Value[Text]
      case class F64(value: Double) extends Value[Float64]
      case object EmptyRecord extends Value[Record[EmptyResource]]
      case class ExtendRecord[A, Name <: String, T](
        init: Value[A],
        name: Name,
        last: Value[T],
      ) extends Value[A ### (Name of T)]

      override def unit: Value[EmptyResource] =
        Unit

      override def pair[A, B](a: Value[A], b: Value[B]): Value[A ** B] =
        Pair(a, b)

      override def text(value: String): Value[Text] =
        Txt(value)

      override def textGet(value: Value[Text]): String =
        value match {
          case Txt(s) => s
          case other =>
            val msg = s"Unexpected Value[Text]: $other"
            Console.err.println(msg)
            throw new AssertionError(msg)
        }

      override def float64(value: Double): Value[Float64] =
        F64(value)

      override def float64Get(value: Value[Float64]): Double =
        value match {
          case F64(d) => d
          case other =>
            val msg = s"Unexpected Value[Float64]: $other"
            Console.err.println(msg)
            throw new AssertionError(msg)
        }

      override def emptyRecord: Value[Record[EmptyResource]] =
        EmptyRecord

      override def record[K <: String & Singleton, T](key: K, value: Value[T]): Value[Record[K of T]] =
        value

      override def extendRecord[A, Name <: String, T](
        init: Value[A],
        name: Name,
        last: Value[T],
      ): Value[A ### (Name of T)] =
        ExtendRecord(init, name, last)
    }


    private class ExecutionImpl[EXN <: executor.Execution](val underlying: EXN) extends MashupExecution {
      override type InPort[A]  = underlying.InPort[A]
      override type OutPort[A] = underlying.OutPort[A]

      override object InPort extends InPorts {
        override def contramap[A, B](port: InPort[B])(f: Fun[A, B]): InPort[A] =
          underlying.InPort.contramap(port)(f)

        override def split[A, B](port: InPort[A ** B]): (InPort[A], InPort[B]) =
          underlying.InPort.split(port)

        override def emptyResourceIgnore(port: InPort[EmptyResource]): Unit =
          underlying.InPort.discardOne(port)

        override def functionInputOutput[I, O](port: InPort[I --> O]): (OutPort[I], InPort[O]) =
            underlying.InPort.functionInputOutput(port)

        override def choiceAwait[A, B](port: InPort[A |&| B]): Async[Try[Either[InPort[A], InPort[B]]]] =
          underlying.InPort.supplyChoice(port).map(_.toTry)

        override def unlimitedAwaitChoice[A](
          port: InPort[Unlimited[A]],
        ): Async[Try[Option[Either[InPort[A], (InPort[Unlimited[A]], InPort[Unlimited[A]])]]]] = {
          val port1 = underlying.InPort.contramap(port)(StarterKit.coreLib.Unlimited.fromChoice[A])
          underlying.InPort.supplyChoice(port1)
            .flatMap {
              case Left(e) =>
                Async.now(Failure(e))
              case Right(Left(empty)) =>
                underlying.InPort.discardOne(empty)
                Async.now(Success(None))
              case Right(Right(port)) =>
                underlying.InPort.supplyChoice(port)
                  .flatMap {
                    case Left(e) =>
                      Async.now(Failure(e))
                    case Right(Left(portSingle)) =>
                      Async.now(Success(Some(Left(portSingle))))
                    case Right(Right(portSplit)) =>
                      val (port1, port2) = underlying.InPort.split(portSplit)
                      Async.now(Success(Some(Right((port1, port2)))))
                  }
            }
        }

        override def float64Supply(port: InPort[Float64], value: Double): Unit =
          underlying.InPort.supplyVal(port, value)

        override def textSupply(port: InPort[Text], value: String): Unit =
          underlying.InPort.supplyVal(port, value)

        override def valueSupply[A](port: InPort[A], value: Value[A]): Unit =
          value match {
            case Value.Unit        => underlying.InPort.discardOne(port)
            case Value.Txt(value)  => underlying.InPort.supplyVal[String](port, value)
            case Value.F64(value)  => underlying.InPort.supplyVal[Double](port, value)
            case Value.EmptyRecord => underlying.InPort.discardOne(port)
            case p: Value.Pair[x, y]  =>
              val (px, py) = underlying.InPort.split[x, y](port)
              valueSupply(px, p.a)
              valueSupply(py, p.b)
            case ext: Value.ExtendRecord[x, _, y] =>
              val (initPort, lastPort) = underlying.InPort.split[x, y](port)
              valueSupply(initPort, ext.init)
              valueSupply(lastPort, ext.last)
          }

        override def labeledGet[Label <: String & Singleton, T](port: InPort[Label of T]): InPort[T] =
          port
      }

      override object OutPort extends OutPorts {
        override def map[A, B](port: OutPort[A])(f: Fun[A, B]): OutPort[B] =
          underlying.OutPort.map(port)(f)

        override def split[A, B](port: OutPort[A ** B]): (OutPort[A], OutPort[B]) =
          underlying.OutPort.split(port)

        override def emptyResourceIgnore(port: OutPort[EmptyResource]): Unit =
          underlying.OutPort.discardOne(port)

        override def functionInputOutput[I, O](port: OutPort[I --> O]): (InPort[I], OutPort[O]) =
          underlying.OutPort.functionInputOutput(port)

        override def chooseLeft[A, B](port: OutPort[A |&| B]): OutPort[A] =
          underlying.OutPort.chooseLeft(port)

        override def chooseRight[A, B](port: OutPort[A |&| B]): OutPort[B] =
          underlying.OutPort.chooseRight(port)

        override def unlimitedIgnore[A](port: OutPort[Unlimited[A]]): Unit = {
          val port1 = underlying.OutPort.map(port)(StarterKit.coreLib.Unlimited.discard[A])
          underlying.OutPort.discardOne(port1)
        }

        override def unlimitedGetSingle[A](port: OutPort[Unlimited[A]]): OutPort[A] =
          underlying.OutPort.map(port)(StarterKit.coreLib.Unlimited.single[A])

        override def unlimitedSplit[A](port: OutPort[Unlimited[A]]): (OutPort[Unlimited[A]], OutPort[Unlimited[A]]) = {
          val ports = underlying.OutPort.map(port)(StarterKit.coreLib.Unlimited.split)
          underlying.OutPort.split(ports)
        }

        override def float64Get(port: OutPort[Float64]): Async[Try[Double]] =
          underlying.OutPort.awaitVal(port).map(_.toTry)

        override def textGet(port: OutPort[Text]): Async[Try[String]] =
          underlying.OutPort.awaitVal(port).map(_.toTry)

        override def valueGet[A](port: OutPort[A])(using ev: ValueType[A]): Async[Try[Value[A]]] =
          ev.readFrom(using RuntimeImpl.this, ExecutionImpl.this)(port)

        override def recordIgnoreEmpty(port: OutPort[Record[EmptyResource]]): Unit =
          underlying.OutPort.discardOne(port)

        override def recordGetSingle[N <: String, T](port: OutPort[Record[N of T]]): OutPort[T] =
          port

        override def recordUnsnoc[A, N <: String, T](port: OutPort[A ### (N of T)]): (OutPort[A], OutPort[T]) =
          underlying.OutPort.split(port)
      }
    }
  }
}
