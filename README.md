# Libretto

Declarative concurrency and stream processing library for Scala.

## Motivation

... or why another concurrency and stream processing library.

Libretto grew out of frustration with existing libraries. Here is an attempt to summarize the pain points.

- **Dissatisfaction with effects being a prerequisite for concurrency.**

  Existing libraries tend to build concurrency on top of effects:
  completing a `Promise` is an effect,
  spawning an actor or a fiber is an effect,
  enqueueing a message in a queue is an effect.
  
  Libretto rejects the assumption that effects are a prerequisite for concurrency.

  Although stream processing libraries do provide some high-level operations for declarative concurrency that abstract
  away from the underlying effects, we haven't come across a library with a set of high-level operations that
  is expressive enough for a moderately complex application.

- **Underdelivery on the promise of writing mere _descriptions_ or _blueprints_ of programs.**

  (Even in an `IO` monad style program) we still manipulate live objects with identities, such as fibers, mutable
  references, queues, "pre-materialized" blueprints, ...
  
  That does not fit our idea of writing mere descriptions of programs.

- **The cogintive load of making sure all the wires are connected.**

  In ensuring that

    * each `Promise` is completed and completed only once,
    * every spawned computation (`Future`, actor, fiber) is awaited,
    * all streams are consumed, all sinks are fed,
    * all messages from a queue are processed (or _intentionally_ discarded),

  programmers are typically left on their own, with no help from the type system.

- **Callbacks everywhere.**

  It is disappointing how callback-ridden our programs, including functional programs, are when it comes to concurrency
  and accessing resources.

  By a _callback_ we mean a function object that performs effects (on resources it has captured) and is passed to
  someone else to be executed.

  One common example of a callback-style interface is an HTTP server taking, during construction, a request handler
  callback. The request handler has captured resources, such as a reference to mutable state or a database connector,
  and performs side-effects on them.

  The problem with callbacks is that they create non-local interaction, which makes it hard to reason about programs.

- **Lack of expressivity of the high-level stream operations.**

  Building custom dataflow topologies with existing libraries, if at all possible,
  requires escaping to a different paradigm, one which is more low-level and imperative.

  We are talking about that case when you needed a slight variation on a stream operator and ended up "manually"
  shoveling messages between queues, mutable references and promises.

- **Inability to express protocols of interaction in types.**

  In practice this leads to having to handle a lot of illegal state.

  To give an example, consider a protocol between two components, Alice and Bob, according to which Alice sends `A`
  to Bob, Bob replies with `B` or `C`, and then Alice replies with `D` if Bob sent `B` and with `E` if Bob sent `C`.

  In a common (but unsatisfactory) implementation, Bob formally accepts any of `A`, `D`, `E` at all times and raises
  or replies with an error if the protocol is violated, i.e. if it is not in a state in which it can accept the message.

## Design Goals

- **Expressiveness.** Make many things representable and make the representations natural.

  Dynamic stream topologies are readily expressible, without needing built-in support.
  Even a stream itself is not a primitive, but derived from the other primitives.
  That gives confidence that when you need something other than what is provided out-of-the-box,
  you will be able to build it out of the provided primitives, without escaping to a different paradigm.

- **Ease of reasoning about programs.** Libretto aims to achieve this goal via:

  - **Direct-style** programming, in which _all_ interaction of a component with its environment is stated by its
    type signature (much like inputs and outputs of a pure function).

    This is in contrast to callback-style described above and leading to spooky action at a distance.

    Direct-style programming is possible thanks to Libretto's ability to express interaction protocols (session types)
    in a component's interface.  

  - **Declarativeness.**

    _“Progress is possible only if we train ourselves to think about programs
    without thinking of them as pieces of executable code.”_ -- Edsger W. Dijkstra
    
  - **Graphical notation.** We are often able to visualize the architecture of a system as a diagram, but there is
    usually a big gap between the diagram and the code.
    
    Libretto primitives have graphical notation that composes into larger diagrams as we compose the program,
    preserving close correspondence between code and graphical representation.

- **Strong static guarantees.** It is guaranteed at compile time that every producer is connected to a consumer.
  Typed protocols (session types) are checked at compile time for type safety.

- **Programs as data.** Libretto programs are just data structures.
  
  Note that unlike monad-based programs, which are also just values, Libretto programs are not hidden inside
  an inscrutable Scala function after the first `flatMap`.
  
  As such, Libretto programs can be inspected, manipulated, optimized, given different interpretations, ...

## Libretto in a Nutshell

Libretto takes inspiration from linear logic, with a twist of interpreting the multiplicative conjunction
in a concurrent fashion.

The correspondence of linear logic to certain monoidal categories led to a point-free notation that enforces linearity
statically, despite the lack of linear types in the host language.

Primitives for racing and recursion were added.

## Documentation

[Scaladoc](https://tomasmikula.github.io/libretto/scaladoc/snapshot/api/) (Found something undocumented or not documented clearly? We should do better. Do not hesitate to
[submit a documentation request](https://github.com/TomasMikula/libretto/issues/new?labels=documentation).)

[Tutorial](tutorial/basics.md)

## Caveats

It is all too common for software projects to highlight only the good parts or to overstate their features.
We value your time and want to be absolutely honest about the limitations.
However, it is hard to know what we are missing.
That's why we need your help.

Do you find that libretto does not hold up to some of its promises?
Do you find that the project description omits some important limitation?
Do you feel that you have spent too much time to find out something that could have been presented more readily?
Please, [let us know](https://github.com/TomasMikula/libretto/issues/new?labels=criticism).

**Batteries not included.** The streams library is under-developed. I/O library (file, network) is non-existent
at the moment. There are currently no connectors or wrappers for things like HTTP servers, DB connectors,
message brokers, ...

**Not yet a good story for supervision/error recovery.**

**Flawed proof-of-concept implementation.**
The current implementation [is leaky](https://github.com/TomasMikula/libretto/issues/46). It is not a design flaw,
just an implementation flaw.

**Point-free style _is_ cumbersome.**
This is the price for statically checked linearity, but there's no hiding it is a pain.

**Best practices not established.**
Programming in Libretto is quite different from conventional concurrency libraries. It is not clear what the best
practices should be.

**Not used to this level of concurrency.**
In conventional programming languages and libraries, concurrency is a scarce special thing. In Libretto, concurrency
is the default and sequentiality is a special thing. The consequences might be surprising.


## Q&A

Did not find an answer to your question?
Do not hesitate to [ask us](https://github.com/TomasMikula/libretto/issues/new?labels=question).

### What is Libretto for?

Libretto is a library for implementing concurrent systems and stream processing in Scala.
Its focus is on the programming model, i.e. the generic glue to structure concurrent programs,
rather than any specific use cases.

### Who is Libretto for?

You are more likely to appreciate Libretto if you:
 - cannot function without static types;
 - are into functional and/or declarative programming;
 - like when the compiler is guiding you (type-driven development);
 - hate falling back to imperative code (like the `IO` monad) when it comes to concurrency;
 - have hit an expressiveness limit of an existing library when you needed a slightly non-trivial data-flow topology.

### Is Libretto production-ready?

No. See also [Caveats](#caveats).

The goal for now is to present a different approach to concurrent programming
and to excite a small number of enthusiasts to play with it, explore it and push it further.

The expectaion is that people will find the Libretto approach worthwhile regardless of
unstable API, non-existent ecosystem of libraries, flawed proof-of-concept implementation,
cumbersome point-free notation, or unknown performance characteristics.

### What do you mean by _declarative,_ anyway?

Declarative programming is a programming paradigm in which we _describe_ the computation
without giving instructions to the underlying execution model.
Examples of such instructions are updating a shared mutable variable or spawning or joining a thread/fiber/actor.

Instructions to the underlying execution model are _side-effects,_ so we can say that
declarative programs are programs without side-effects.
In particular, all expressions in a declarative program must be _referentially transparent._

### Aren't `IO` monad-style programs referentially transparent as well?

Not really.

They _are_ referentially transparent from the point of view of the host language (Scala).
The expression `IO { println("Hi!") }` is referentially transparent in that given

```scala
val x = IO { println("Hi!") }
```

we can freely replace occurences of `x` by `IO { println("Hi!") }` (and vice versa)
without changing the meaning of the program.
There is no denying that this already has great benefits for compositionality and reasoning about programs.

However, if we view the `IO` monad as a new semantic level and having to wrap some expressions in `IO { ... }`
as just a syntactic annoyance for the sake of embedding `IO` programs in Scala, then referential transparency
at this new `IO` level would require the following two programs to have the same meaning

```scala
for {
  x <- IO { println("Hi!") }
  y <- IO { println("Hi!") }
} yield y
```

```scala
for {
  x <- IO { println("Hi!") }
  y <- IO { x }
} yield y
```

but they do not.

Saying that (the expressions in) these programs are referentially transparent (even though at the Scala level they are)
is somewhat like saying that any program is referentially transparent when viewed as a text file in a file system.

Note: The way Libretto circumvents the issue of programs like these having different behavior is _linearity:_
If, by some stretch of the imagination, these were Libretto programs, the first one would not typecheck,
because `x` is unused.

### How can libretto _statically_ guarantee that each resource is consumed exactly once when Scala does not have linear type system features?

### Why do I have to write libretto programs in that strange point-free style?

### What exactly are the primitives of Libretto, from which everything else is derived?

### Does libretto support dynamic stream topologies?

### Do libretto streams support feedback loops?

### Is there support for timers?

### How do I communicate with the external world (I/O)?

### Does libretto support supervision of a subsystem?

### Can I execute different parts of the system on different execution contexts/thread pools?

### Does libretto have fibers, as known from ZIO or Cats Effect?

### Where is the monadic structure in Libretto?

### You criticize monadic IO for hiding the program structure inside impenetrable Scala functions. However, Libretto allows to incorporate Scala functions and dynamically computed Scala values into the system as well. Are Libretto programs any more amenable to inspection than IO programs?

### Does libretto support session types?

### Why are there two different function-like symbols? What is the difference between `-⚬` and  `=⚬`?

|         `-⚬`         |          `=⚬`           | notes |
|:--------------------:|:-----------------------:|-------|
| Describes a program. | Lives inside a program. |       |
| Tangible: we create and manipulate _Scala_ values of this type. | Intangible: there are no _Scala_ values of this type. A type like `A =⚬ B` can appear only to the left or right of `-⚬`. |  |
| Pure value. As such, it can be used any number of times (including zero). | Must be treated as a resource, i.e. consumed (evaluated) exactly once, because it might have captured other resources that are consumed on evaluation. |  |
| Morphism | Object, Internal Hom | In category theory, one does not look inside objects. Everything is expressed in terms of morphisms. In particular, objects are not viewed as collections of elements. Analogously, there are no values of type `=⚬`, or of types <code>&#124;*&#124;</code>, <code>&#124;+&#124;</code>, <code>&#124;&amp;&#124;</code>, `One`, `Val`, ... These are all objects in a category and we do not view them as collections of elements. We express everything in terms of morphisms, `-⚬`. |

### How do I type the `⚬` symbol used in `-⚬` and `=⚬`?

### Does Libretto prevent deadlocks?

No. It is easy to write a Libretto program that gets stuck because of cyclic dependencies.

Some concurrency libraries that claim to prevent deadlocks use the word deadlock in a very specific sense,
namely _system threads_ waiting on each other in a cycle. _Thread_ is not even a term from Libretto's vocabulary,
but you can safely assume that any implementation of Libretto does not cause deadlocks on the level of threads, either.

### Could deadlocks be prevented statically, in principle?

Yes.

Trivially, by restricting the DSL so that it is impossible to set up a loop in the data flow.
However, the resulting loss of expressiveness would make it unusable for most applications.

A sufficiently expressive deadlock-free DSL would certainly require more sophisticated types.
We are leaving that for further research and most likely for a different host language than Scala.

### Why do we need negative values?

To avoid callbacks in bidirectional dataflows.

A negative value `Neg[A]` could alternatively be expressed as a callback `Val[A] =⚬ One`, but we want to avoid callbacks.

### What's the problem with callbacks?

 - Indirection, resource capture, side-effects, non-local interaction.
   * The consumer of a value, instead of stating in its interface the need for a value to be supplied, prepares
     a function object that typically captures some resources (i.e. it is a closure) and performs side-effects on them.
   * The producer of a value, instead of stating in its interface that it produces a value, is aksed to invoke
     the callback, which from its perspective is some foreign code, on the produced value.
   * Through the captured resources and side-effects on them, the invocation of a callback causes spooky action
     at a distance, which negatively affects the ability to reason about programs.
 - Moreover, components that produce or consume callbacks are _higher-order_ linear functions in Libretto.
   Higher-order functions are more powerful than first-order functions. (In terms of category theory, higher-order
   functions require closedness of the category.) By the principle of least power, we should avoid high-order functions,
   and thus callbacks, when possible.

## Copyright and License

Copyright 2020–2021 Tomas Mikula

This software is distributed under the Mozilla Public License 2.0, see the LICENSE file for details.
