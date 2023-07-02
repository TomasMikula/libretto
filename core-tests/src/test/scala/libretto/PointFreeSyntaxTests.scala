package libretto

import libretto.testing.TestCase
import libretto.testing.scalatest.scaletto.ScalatestScalettoTestSuite
import libretto.testing.scaletto.ScalettoTestKit

class PointFreeSyntaxTests extends ScalatestScalettoTestSuite {

  override def testCases(using kit: ScalettoTestKit): List[(String, TestCase[kit.type])] =
    List()

}
