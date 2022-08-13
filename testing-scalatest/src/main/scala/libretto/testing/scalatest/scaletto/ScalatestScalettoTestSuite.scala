package libretto.testing.scalatest.scaletto

import libretto.testing.scalatest.ScalatestSuite
import libretto.testing.scaletto.{ScalettoTestKit, ScalettoTestSuite}

abstract class ScalatestScalettoTestSuite
extends ScalatestSuite[ScalettoTestKit]
   with ScalettoTestSuite
