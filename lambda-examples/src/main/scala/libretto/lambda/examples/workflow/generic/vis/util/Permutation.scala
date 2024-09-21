package libretto.lambda.examples.workflow.generic.vis.util

import scala.{collection as sc}
import scala.collection.mutable
import scala.collection.generic.CanBuildFrom

class Permutation private(
  private[Permutation] val value: sc.Seq[Int]
) {
  import Permutation.*

  def length: Int =
    value.length

  def permute[A](src: sc.IndexedSeq[A]): Permuting[A] =
    Permuting[A](src, this)

  def unpermute[A](src: sc.IndexedSeq[A]): Permuting[A] =
    this.invert.permute(src)

  def invert: Permutation = {
    val res = new Array[Int](value.length)
    value.iterator.zipWithIndex.foreach { case (v, i) =>
      res(v) = i
    }
    Permutation(res)
  }
}

object Permutation {

  class Permuting[A] private[Permutation](src: sc.IndexedSeq[A], perm: Permutation) {
    require(src.length == perm.length)

    def to[CC[_]](using f: sc.Factory[A, CC[A]]): CC[A] =
      val builder = f.newBuilder
      perm.value.foreach { j =>
        builder += src(j)
      }
      builder.result()
  }

  def sort[A: Ordering](arr: Array[A]): (mutable.ArraySeq[A], Permutation) =
    val (sorted, perm) = arr.zipWithIndex.sortInPlaceBy(_._1).unzip
    (sorted, Permutation(perm))
}
