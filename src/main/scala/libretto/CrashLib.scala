package libretto

object CrashLib {
  def apply(
    dsl: CrashDSL,
    lib: CoreLib[dsl.type],
  ): CrashLib[dsl.type, lib.type] =
    new CrashLib(dsl, lib)
}

class CrashLib[DSL <: CrashDSL, Lib <: CoreLib[DSL]](
  val dsl: DSL,
  val lib: Lib with CoreLib[dsl.type],
) {
  import dsl._
  import lib._

  def crashPos[A](msg: String)(implicit A: Junction.Positive[A]): A -⚬ A =
    id                                 [          A ]
      .introFst(done)               .to[ Done |*| A ]
      .>(crash[A, A](msg))          .to[ Done |*| A ]
      .joinL                        .to[          A ]
      
  def crashNeg[A](msg: String)(implicit A: Junction.Negative[A]): A -⚬ A =
    id                                 [          A ]
      .<.un(elimFst(need))        .from[ Need |*| A ]
      .<.un(cocrash[A, A](msg))   .from[ Need |*| A ]
      .<.un(A.awaitNeg)           .from[          A ]
}
