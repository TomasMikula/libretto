package kindville

@main
def main: Unit =
  val seven: Int =
    7.unmask[Int, TNil](using TypeApp.nullary[Int])
  val opt7: Option[Int] =
    Option(7).unmask[Option, Int :: TNil](using TypeApp[Option, Option[Int]])
  val mapIS: Map[Int, String] =
    Map(7 -> "seven").unmask[Map, Int :: String :: TNil](using TypeApp[Map, Map[Int, String]])

  TypeApp[List, List[Int]]
  TypeApp[TypeApp, TypeApp[Int, Int, Int]]
