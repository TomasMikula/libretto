package libretto.testing

import libretto.testing.TestKit.dsl
import libretto.util.Monad.syntax._
import scala.{:: => NonEmptyList}

sealed trait Tests {
  type Kit <: TestKit

  def testCases(using kit: Kit): NonEmptyList[(String, Tests.Case[kit.type])]

  val testExecutors: NonEmptyList[TestExecutor[Kit]]
}

object Tests {
  def writtenUsing[TK <: TestKit]: Builder.WrittenUsing[TK] =
    new Builder.WrittenUsing[TK]()

  object Builder {
    class WrittenUsing[TK <: TestKit]() {
      def executedBy(
        executor: TestExecutor[TK],
        executors: TestExecutor[TK]*,
      ): ExecutedBy[TK] =
        new ExecutedBy[TK](NonEmptyList(executor, executors.toList))
    }

    class ExecutedBy[TK <: TestKit](executors: NonEmptyList[TestExecutor[TK]]) {
      def in(
        cases: (kit: TK) ?=> Cases[kit.type],
      ): Tests =
        new Tests {
          override type Kit = TK
          override def testCases(using kit: TK) = cases.values
          override val testExecutors = executors
        }
    }
  }

  sealed trait Cases[TK <: TestKit] {
    def values(using kit: TK): NonEmptyList[(String, Case[kit.type])]
  }

  object Cases {
    def apply(using kit: TestKit)(
      testCase: (String, Case[kit.type]),
      moreCases: (String, Case[kit.type])*,
    ): Cases[kit.type] =
      new Cases[kit.type] {
        override def values(using testKit: kit.type): NonEmptyList[(String, Case[testKit.type])] =
          NonEmptyList(testCase, moreCases.toList)
      }
  }

  sealed trait Case[TK <: TestKit]

  object Case {

    sealed trait Single[TK <: TestKit] extends Case[TK] {
      val testKit: TK
      import testKit.Outcome
      import testKit.dsl._
      import testKit.probes.OutPort

      type O
      type X

      val body: Done -⚬ O

      val conductor: OutPort[O] => Outcome[X]

      val postStop: X => Outcome[Unit]
    }

    case class Multiple[TK <: TestKit](
      cases: List[(String, Case[TK])],
    ) extends Case[TK]

    private def make[A, B](using
      kit: TestKit,
    )(
      body0: dsl.-⚬[dsl.Done, A],
      conductor0: kit.probes.OutPort[A] => kit.Outcome[B],
      postStop0: B => kit.Outcome[Unit],
    ): Case[kit.type] =
      new Single[kit.type] {
        override type O = A
        override type X = B
        override val testKit = kit
        override val body = body0
        override val conductor = conductor0
        override val postStop = postStop0
      }

    def apply(using kit: TestKit)(body: dsl.-⚬[dsl.Done, kit.Assertion[dsl.Done]]): Case[kit.type] =
      make(body, kit.extractOutcome, kit.monadOutcome.pure)

    def apply[O](using kit: TestKit)(
      body: kit.dsl.-⚬[kit.dsl.Done, O],
      conduct: kit.probes.OutPort[O] => kit.Outcome[Unit],
    ): Case[kit.type] =
      make[O, Unit](body, conduct, kit.monadOutcome.pure)

    def apply[A, B](using kit: TestKit)(
      body: kit.dsl.-⚬[kit.dsl.Done, A],
      conduct: kit.probes.OutPort[A] => kit.Outcome[B],
      postStop: B => kit.Outcome[Unit],
    ): Case[kit.type] =
      make[A, B](body, conduct, postStop)

    def multiple[TK <: TestKit](
      cases: (String, Case[TK])*,
    ): Case[TK] =
      Multiple[TK](cases.toList)

    def interactWith[O](using kit: TestKit)(body: kit.dsl.-⚬[kit.dsl.Done, O]): InteractWith[kit.type, O] =
      InteractWith(kit, body)

    object InteractWith {
      def apply[O](kit: TestKit, body: kit.dsl.-⚬[kit.dsl.Done, O]): InteractWith[kit.type, O] =
        new InteractWith(kit, body)
    }

    class InteractWith[TK <: TestKit, O](
      val kit: TK,
      val body: kit.dsl.-⚬[kit.dsl.Done, O],
    ) {
      def via(conductor: kit.probes.OutPort[O] => kit.Outcome[Unit]): Case[kit.type] =
        Case(using kit)(body, conductor)

      def via[X](
        conductor: kit.probes.OutPort[O] => kit.Outcome[X],
        postStop: X => kit.Outcome[Unit],
      ): Case[kit.type] =
        Case(using kit)(body, conductor, postStop)
    }
  }
}
