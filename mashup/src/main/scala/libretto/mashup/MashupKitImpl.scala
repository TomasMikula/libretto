package libretto.mashup

import libretto.{ScalaExecutor, StarterKit, scalasource}
import libretto.util.Async
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success, Try}
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

    override type Unlimited[A] = StarterKit.coreLib.Unlimited[A]

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

    override object Unlimited extends Unlimiteds {
      export StarterKit.coreLib.Unlimited.map
    }
  }

  override def createRuntime(executor: ScheduledExecutorService): MashupRuntime[dsl.type] = {
    val exec = StarterKit.executor(executor)(executor)
    new RuntimeImpl(exec)
  }

  private class RuntimeImpl(
    executor: ScalaExecutor.Of[StarterKit.dsl.type, Future],
  ) extends MashupRuntime[dsl.type] {
    override val dsl: kit.dsl.type = kit.dsl
    import dsl.{-->, EmptyResource, Unlimited}

    override opaque type InPort[A]  = executor.InPort[A]
    override opaque type OutPort[A] = executor.OutPort[A]
    override opaque type Execution  = executor.Execution

    override def run[A, B](prg: dsl.Fun[A, B]): (InPort[A], OutPort[B], Execution) =
      executor.execute(prg)

    override object InPort extends InPorts {
      override def emptyResourceIgnore(port: InPort[EmptyResource]): Unit =
        executor.InPort.discardOne(port)

      override def functionInputOutput[I, O](port: InPort[I --> O]): Async[(OutPort[I], InPort[O])] =
        Async.unsafeFromFuture(
          executor.InPort.functionInputOutput(port),
          onError = e => Console.err.println(s"Unexpected failure of InPort.functionInputOutput: $e") // XXX
        )

      override def unlimitedAwaitChoice[A](
        port: InPort[Unlimited[A]],
      )(
        exn: Execution, // TODO: execution should be built into InPort
      ): Async[Try[Option[Either[InPort[A], (InPort[Unlimited[A]], InPort[Unlimited[A]])]]]] = {
        val ft: Future[Try[Option[Either[InPort[A], (InPort[Unlimited[A]], InPort[Unlimited[A]])]]]] =
          executor.InPort.contramap(port)(StarterKit.coreLib.Unlimited.fromChoice[A])(exn)
            .flatMap { port =>
              executor.InPort.supplyChoice(port)
                .flatMap {
                  case Left(e) =>
                    Future.successful(Failure(e))
                  case Right(Left(empty)) =>
                    executor.InPort.discardOne(empty)
                      .map(_ => Success(None))(ExecutionContext.parasitic) // XXX
                  case Right(Right(port)) =>
                    executor.InPort.supplyChoice(port)
                      .flatMap {
                        case Left(e) =>
                          Future.successful(Failure(e))
                        case Right(Left(portSingle)) =>
                          Future.successful(Success(Some(Left(portSingle))))
                        case Right(Right(portSplit)) =>
                          executor.InPort.split(portSplit)
                            .map { case (port1, port2) =>
                              Success(Some(Right((port1, port2))))
                            } (ExecutionContext.parasitic) // XXX
                      } (ExecutionContext.parasitic) // XXX
                } (ExecutionContext.parasitic) // XXX
            } (ExecutionContext.parasitic) // XXX
        Async.unsafeFromFuture(
          ft,
          e => Console.err.println(s"Unexpected failure of InPort.supplyChoice: $e"), // XXX
        )
      }
    }

    override object OutPort extends OutPorts {
      override def emptyResourceIgnore(port: OutPort[EmptyResource]): Unit =
        executor.OutPort.discardOne(port)

      override def functionInputOutput[I, O](port: OutPort[I --> O]): Async[(InPort[I], OutPort[O])] =
        Async.unsafeFromFuture(
          executor.OutPort.functionInputOutput(port),
          onError = e => Console.err.println(s"Unexpected failure of OutPort.functionInputOutput: $e") // XXX
        )

      override def unlimitedIgnore[A](port: OutPort[Unlimited[A]])(exn: Execution): Unit =
        executor.OutPort.map(port)(StarterKit.coreLib.Unlimited.discard[A])(exn)
          .flatMap { port => executor.OutPort.discardOne(port) } (ExecutionContext.parasitic) // XXX

      override def unlimitedGetSingle[A](port: OutPort[Unlimited[A]])(
        exn: Execution, // TODO: execution should be built into OutPort
      ): Async[OutPort[A]] =
        Async.unsafeFromFuture[OutPort[A]](
          executor.OutPort.map(port)(StarterKit.coreLib.Unlimited.single[A])(exn),
          onError = e => Console.err.println(s"Unexpected failure of OutPort.map: $e") // XXX
        )

      override def unlimitedSplit[A](port: OutPort[Unlimited[A]])(exn: Execution): Async[(OutPort[Unlimited[A]], OutPort[Unlimited[A]])] =
        Async.unsafeFromFuture(
          executor.OutPort.map(port)(StarterKit.coreLib.Unlimited.split)(exn)
            .flatMap { port =>
              executor.OutPort.split(port)
            } (ExecutionContext.parasitic), // XXX
          onError = e => Console.err.println(s"Unexpected failure of OutPort.map: $e") // XXX
        )
    }
  }
}
