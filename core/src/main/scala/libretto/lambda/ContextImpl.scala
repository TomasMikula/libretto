package libretto.lambda

import scala.collection.mutable

class ContextImpl[-⚬[_, _], |*|[_, _], V](
  parent: Option[ContextImpl[-⚬, |*|, V]] = None,
) {
  case class Entry[A](
    split: Option[A -⚬ (A |*| A)],
    discard: Option[[B] => Unit => (A |*| B) -⚬ B],
  )

  val m: mutable.Map[Var[V, Any], Entry[Any]] =
    mutable.Map.empty

  def register[A](v: Var[V, A])(
    split: Option[A -⚬ (A |*| A)],
    discard: Option[[B] => Unit => (A |*| B) -⚬ B],
  ): Unit =
    m.updateWith(
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

  def getSplit[A](v: Var[V, A]): Option[A -⚬ (A |*| A)] =
    m.get(v.asInstanceOf[Var[V, Any]])
      .flatMap(_.asInstanceOf[Entry[A]].split)
      .orElse(parent.flatMap(_.getSplit(v)))

  def getDiscard[A](v: Var[V, A]): Option[[B] => Unit => (A |*| B) -⚬ B] =
    m.get(v.asInstanceOf[Var[V, Any]])
      .flatMap(_.asInstanceOf[Entry[A]].discard)
      .orElse(parent.flatMap(_.getDiscard(v)))
}
