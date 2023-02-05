package libretto.lambda

import scala.collection.mutable

class ContextImpl[-⚬[_, _], |*|[_, _], V](
  parent: Option[ContextImpl[-⚬, |*|, V]] = None,
) {
  private case class Entry[A](
    split: Option[A -⚬ (A |*| A)],
    discard: Option[[B] => Unit => (A |*| B) -⚬ B],
  )

  private type Intro[A] = [x] => Unit => x -⚬ (A |*| x)

  private val nonLinearOps: mutable.Map[Var[V, Any], Entry[Any]] =
    mutable.Map.empty

  private val constants: mutable.Map[Var[V, Any], Intro[Any]] =
    mutable.Map.empty

  def newVar[A](data: V): Var[V, A] =
    new Var[V, A](data, this)

  def isDefiningFor[A](v: Var[V, A]): Boolean =
    v.context eq this

  def register[A](v: Var[V, A])(
    split: Option[A -⚬ (A |*| A)],
    discard: Option[[B] => Unit => (A |*| B) -⚬ B],
  ): Unit =
    nonLinearOps.updateWith(
      v.asInstanceOf[Var[V, Any]],
    ) {
      case None =>
        Some(Entry[A](split, discard).asInstanceOf[Entry[Any]])
      case Some(e0) =>
        val e = e0.asInstanceOf[Entry[A]]
        Some(
          Entry[A](
            split orElse e.split,
            discard orElse e.discard,
          ).asInstanceOf[Entry[Any]]
        )
    }

  def registerConstant[A](v: Var[V, A])(
    introduce: [x] => Unit => x -⚬ (A |*| x),
  ): Unit =
    constants.put(
      v.asInstanceOf[Var[V, Any]],
      (introduce: Intro[A]).asInstanceOf[Intro[Any]],
    )

  def getSplit[A](v: Var[V, A]): Option[A -⚬ (A |*| A)] =
    nonLinearOps.get(v.asInstanceOf[Var[V, Any]])
      .flatMap(_.asInstanceOf[Entry[A]].split)
      .orElse(parent.flatMap(_.getSplit(v)))

  def getDiscard[A](v: Var[V, A]): Option[[B] => Unit => (A |*| B) -⚬ B] =
    nonLinearOps.get(v.asInstanceOf[Var[V, Any]])
      .flatMap(_.asInstanceOf[Entry[A]].discard)
      .orElse(parent.flatMap(_.getDiscard(v)))

  def getConstant[A](v: Var[V, A]): Option[[x] => Unit => x -⚬ (A |*| x)] =
    constants
      .get(v.asInstanceOf[Var[V, Any]])
      .asInstanceOf[Option[[x] => Unit => x -⚬ (A |*| x)]]
      .orElse(parent.flatMap(_.getConstant(v)))
}
