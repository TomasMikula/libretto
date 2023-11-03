package libretto.lambda

trait StrongZippable[|*|[_, _], F[_]] extends Zippable[|*|, F] with Unzippable[|*|, F]
