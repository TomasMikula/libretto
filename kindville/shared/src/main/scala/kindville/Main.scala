package kindville

import scala.annotation.experimental

@experimental
@main
def main: Unit =
  val seven: Int =
    7.unmask[Int, TNil](using TypeApp.inferArgs[Int, Int])
  val opt7: Option[Int] =
    Option(7).unmask[Option, Int :: TNil](using TypeApp.inferArgs[Option, Option[Int]])
  val mapIS: Map[Int, String] =
    Map(7 -> "seven").unmask[Map, Int :: String :: TNil](using TypeApp.inferArgs[Map, Map[Int, String]])

  TypeApp.inferArgs[List, List[Int]]
  TypeApp.inferArgs[TypeApp, TypeApp[Int, Int, Int]]

  // println(encoderOf[[P, Q] =>> Map[P, Q], Unit]([As, FAs] => (value: FAs, ev: TypeApp[Map, As, FAs]) => ()))
  // println(termStructureOf([x, y] => (m: Map[x, y]) => m.size))
  println(typeStructureOf[[f[_], g[_[_]]] =>> Map[f[Int], g[f]]])
  // println(termStructureOf(new PolyFunction { override def apply[x, y](m: Map[x, y]): Int = m.size }))

  val x: [A] => Map[Int, A] => Int =
    encoderOf[[Q] =>> Map[Int, Q], Int](
      [As, FAs] => (value: FAs, ev: TypeApp[[Q] =>> Map[Int, Q], As, FAs]) => 42,
    )
  // println(x)
  // println(x[Char](Map(7 -> '7')))
  // println(encoderOf[[X, Y] => List[X] => Option[Y], Unit]([As, FAs] => (value: FAs, ev: TypeApp[[X, Y] => List[X] => Option[Y], As, FAs]) => ()))
