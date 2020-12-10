# Libretto

Declarative concurrency and stream processing library for Scala.

In a nutshell, Libretto took inspiration from linear logic and added concurrent semantics of the multiplicative
conjunction, primitives for racing, and primitive operator for recursion.

## Design Goals

- **Expressiveness.** Libretto aims to be expressive in both meanings of the word, namely in
  - what is possible to represent at all; and
  - how naturally things are represented.

  Things like dynamic stream topologies, feedback loops,
  or session types are readily expressible in Libretto, without them being primitives.

- **Ease of reasoning about programs.** Libretto aims to achieve this goal via:

  - **Direct-style** programming, in which _all_ interaction of a component with its environment is stated by its
    type signature (much like inputs and outputs of a pure function).
    
    This is in contrast to _callback-style,_ in which a component, instead of exposing its output via an interface,
    executes foreign code (a callback) on the produced values. Such callbacks typically perform side-effects
    on captured resources.
    
    <details>
      <summary>Example</summary>
      A common example of callback style is an HTTP server taking a request handler callback. The request handler
      typically captures resources, such as a database connector, and performs side-effects on them. As a result,
      if one encounters such HTTP server in code, it is hard to reason about what it does.
      
      The Libretto alternative is to state in the type signature of the HTTP server that it produces requests and
      for each request eventually requires a response.
    </details>
    
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
  As such, they can be inspected, manipulated, optimized, given different interpretations, ...
  
## Why Another Stream Processing Library

Existing libraries that I know of compromise some or all of the above stated design goals.

Implementing custom dynamic dataflow topologies with existing libraries is either not possible at all or possible only
through escaping to low-level imperative world. In contrast, Libretto has no imperative concepts like
pre-materialization, fibers or signalling variables, yet things like merge, broadcast, feedback loop or even
stream itself are not primitives, but are readily implemented on top of the expressive set of primitives.

Libretto strictly separates the (description of a) program from its execution.
In particular, there are no "blueprints" that are in fact already running.
Libretto programs are just pure values.
Moreover, unlike monad-based programs-as-values, Libretto programs are not hidden inside an inscrutable Scala function
after the first `flatMap`. This opens new possibilities for what can be done with a program.

## Documentation

### Scaladoc

**(TODO)**

Found something undocumented or not documented clearly? We should do better. Do not hesitate to
[submit a documentation request](https://github.com/TomasMikula/libretto/issues/new?labels=documentation).

### Tutorial

**(TODO)**

## Caveats

It is all too common for software projects to highlight only the good parts or to overstate their features.
We want to do better and be absolutely honest about the limitations. However, it is hard to know what we are missing.
That's why we need your help.

Do you find that libretto does not hold up to some of its promises?
Do you find that the project description omits some important limitation?
If you have invested significant time in libretto only to find out that it's not for you,
what information would have saved your time?
Please, [let us know](https://github.com/TomasMikula/libretto/issues/new?labels=criticism).

## FAQs

Did not find an answer to your question?
Do not hesitate to [ask us](https://github.com/TomasMikula/libretto/issues/new?labels=question).

### Is Libretto for me?

Libretto is for anyone who needs to implement concurrent systems or stream processing in Scala.
You are more likely to appreciate Libretto if you:
 - cannot function without static types;
 - are into functional/declarative programming;
 - like when the compiler is guiding you (type-driven development);
 - hate falling back to imperative code (like the `IO` monad) when it comes to concurrency;
 - have hit an expressiveness limit of an existing library when you needed a slightly non-trivial data-flow topology.

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

### Where is the IO monad?

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
