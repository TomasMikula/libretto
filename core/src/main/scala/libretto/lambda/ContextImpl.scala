package libretto.lambda

import scala.collection.mutable

class ContextImpl[-⚬[_, _], |*|[_, _], Var[_]] {
  case class Entry[A](
    split: Option[A -⚬ (A |*| A)],
    discard: Option[[B] => Unit => (A |*| B) -⚬ B],
  )

  val m: mutable.Map[Var[Any], Entry[Any]] =
    mutable.Map.empty

  def register[A](v: Var[A])(
    split: Option[A -⚬ (A |*| A)],
    discard: Option[[B] => Unit => (A |*| B) -⚬ B],
  ): Unit =
    m.updateWith(
      v.asInstanceOf[Var[Any]],
    ) {
      case None =>
        Some(Entry[A](split, discard).asInstanceOf[Entry[Any]])
      case Some(e0) =>
        val e = e0.asInstanceOf[Entry[A]]
        Some(
          Entry[A](
            e.split orElse split,
            e.discard orElse discard,
          ).asInstanceOf[Entry[Any]]
        )
    }

  def getSplit[A](v: Var[A]): Option[A -⚬ (A |*| A)] =
    m.get(v.asInstanceOf[Var[Any]]).flatMap(_.asInstanceOf[Entry[A]].split)

  def getDiscard[A](v: Var[A]): Option[[B] => Unit => (A |*| B) -⚬ B] =
    m.get(v.asInstanceOf[Var[Any]]).flatMap(_.asInstanceOf[Entry[A]].discard)
}
