package libretto.testing

import libretto.util.Monad.syntax._

sealed trait Tests {
  type Kit <: TestKit

  def testCases(using kit: Kit): List[(String, TestCase[kit.type])]

  val testExecutors: List[TestExecutor.Factory[Kit]]
}

object Tests {
  def writtenUsing[TK <: TestKit]: Builder.WrittenUsing[TK] =
    new Builder.WrittenUsing[TK]()

  object Builder {
    class WrittenUsing[TK <: TestKit]() {
      def executedBy(
        executors: TestExecutor[TK] | TestExecutor.Factory[TK]*,
      ): ExecutedBy[TK] =
        new ExecutedBy[TK](
          executors.toList.map {
            case factory: TestExecutor.Factory[TK] => factory
            case executor: TestExecutor[TK]        => TestExecutor.Factory.noOp(executor)
          }
        )
    }

    class ExecutedBy[TK <: TestKit](executors: List[TestExecutor.Factory[TK]]) {
      def in(
        cases: (kit: TK) ?=> List[(String, TestCase[kit.type])],
      ): Tests =
        new Tests {
          override type Kit = TK
          override def testCases(using kit: TK) = cases
          override val testExecutors = executors
        }
    }
  }
}
