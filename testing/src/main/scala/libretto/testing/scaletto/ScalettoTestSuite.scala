package libretto.testing.scaletto

import libretto.testing.{TestCase, TestExecutor, TestSuite}

/** Test suite where all tests are written using [[ScalaTestKit]] (and thus [[libretto.ScalaDSL]]). */
trait AbstractScalettoTestSuite[TK <: ScalettoTestKit] extends TestSuite[TK] {

  extension (TC: TestCase.type)
    def awaitVal[A](using kit: ScalettoTestKit)(
      body: kit.dsl.-⚬[kit.dsl.Done, kit.dsl.Val[A]]
    ): ExpectingVal[kit.type, A] =
      ExpectingVal(kit, body)

  class ExpectingVal[TK <: ScalettoTestKit, A](
    val kit: TK,
    body: kit.dsl.-⚬[kit.dsl.Done, kit.dsl.Val[A]],
  ):
    def checkThat(f: A => kit.Outcome[Unit]): TestCase[kit.type] =
      TestCase
        .interactWith(using kit)(body)
        .via { _.expectVal.flatMap(f) }
}

trait ScalettoTestSuite extends AbstractScalettoTestSuite[ScalettoTestKit] {
  override def testExecutors: List[TestExecutor.Factory[ScalettoTestKit]] =
    List(
      ScalettoTestExecutor.defaultFactory,
    )
}
