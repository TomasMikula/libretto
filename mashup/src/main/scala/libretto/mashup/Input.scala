package libretto.mashup

import libretto.mashup.dsl.{|&|, EmptyResource, of}
import libretto.mashup.rest.RestApi

sealed trait Input[A]

object Input {
  case object Empty extends Input[EmptyResource]
  case class RestApiAt[A](api: RestApi[A], uri: String) extends Input[A]

  sealed trait Choice[Options] extends Input[Options] {
    def and[N <: String & Singleton, A](label: N, a: Input[A]): Choice[Options |&| (N of A)] =
      |&|(label, a)

    def |&|[N <: String & Singleton, A](label: N, a: Input[A]): Choice[Options |&| (N of A)] =
      MultiChoice(this, label, a)
  }

  case class SingleChoice[N <: String & Singleton, A](label: N, input: Input[A]) extends Choice[N of A]
  case class MultiChoice[C, N <: String & Singleton, A](base: Choice[C], label: N, input: Input[A]) extends Choice[C |&| (N of A)]

  def empty: Input[EmptyResource] =
    Empty

  def restApiAt[A](
    api: RestApi[A],
    uri: String,
  ): Input[A] =
    RestApiAt(api, uri)

  def choiceOf[N <: String & Singleton, A](label: N, input: Input[A]): Choice[N of A] =
    SingleChoice(label, input)
}
