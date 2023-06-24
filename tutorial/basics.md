# Libretto Basics

A concurrent program in Libretto DSL is a _pure value_ of a certain type (such as the type `Done -⚬ Done` or
`Done -⚬ Val[String]`).
Such a value is a mere _description,_ or _blueprint,_ of a program to be executed.
The blueprint can then be passed to an interpreter for execution.

Programmer's task is then to write Scala code that first assembles a blueprint and then
passes is to an interpreter for execution. We thus think of run-time as split into
**assembly time** and **execution time**.

## Setup

### sbt project setup

You will need Scala 3 in order to use Libretto. Scala 3 requires a fairly recent version of sbt. Specify the sbt version in your `project/build.properties` file:

```properties
sbt.version=1.9.0
```

In your `build.sbt`, set the Scala version to Scala 3 and add the dependency on Libretto:

```sbt
scalaVersion := "@SCALA_VERSION@"

libraryDependencies += "dev.continuously" %% "libretto-core" % "0.2-M6"
```

Check [search.maven.org](https://search.maven.org/search?q=dev.continuously%20libretto) for the latest version of
Libretto.

### Imports

The code snippets below use these imports:

```scala mdoc
import libretto.scaletto.StarterKit.dsl._
import libretto.scaletto.StarterKit.dsl.$._
```

```scala mdoc:invisible
// types used in the code snippets below
object Types {
  type A
  type B
  type C
  type D
  type E
}
import Types._
```

## Building blocks

Libretto programs are composed of **components** with typed **in-ports** and **out-ports**,
such as this one:

```
┏━━━━━━━━━━━━┓
┞─┐          ┞─┐
╎A│          ╎C│
┟─┘          ┟─┘
┞─┐          ┞─┐
╎B│          ╎D│
┟─┘          ┟─┘
┗━━━━━━━━━━━━┛
```

We draw in-ports on the left and out-ports on the right.

The in-ports and out-ports define the _interface_ of a component.

We can think of a component as a part of a system that runs autonomously and communicates with the rest of the system
through its in-ports and out-ports.

☝️ Do _not_ assume that through in-ports information flows into the component and through out-ports information flows out
of the component. That may or may not be the case. In general, information may flow in either direction or even in both
directions through an in-port as well as through an out-port. However, the distinction between in-ports and out-ports
is important for composition, see below.

## Maximum concurrency

We can be sure that event _e<sub>2</sub>_ happens after event _e<sub>1</sub>_ only if _e<sub>2</sub>_
**causally depends** on _e<sub>1</sub>_. If there is no causal dependence between _e<sub>1</sub>_ and _e<sub>2</sub>_,
then they happen concurrently (☝️ but not necessarily in parallel).

This is different from what most people are used to. It usually takes some work to make things happen concurrently.
In Libretto, it takes some work to make things happen sequentially if there is no natural causal dependence between
them.

As we proceed, we will get an idea of what does and what does not introduce a causal dependence.

## Sequential composition

We can connect an out-port to an in-port (but not to another out-port) of the same type on another component.
For example, these two components `f` and `g`

```
┏━━━━━━━━━━━━┓    ┏━━━━━━━━━━━━┓
┞─┐          ┞─┐  ┞─┐          ┞─┐
╎A│    f     ╎B│  ╎B│    g     ╎C│
┟─┘          ┟─┘  ┟─┘          ┟─┘
┗━━━━━━━━━━━━┛    ┗━━━━━━━━━━━━┛
```

can be composed into a composite component `g ⚬ f`

```
┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
┞─┐                            ┞─┐
╎A│           g ⚬ f            ╎C│
┟─┘                            ┟─┘
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
```

☝️ Although we call it _sequential_ composition, do _not_ assume that`g` takes place "after" `f`, in a temporal or
causal sense. There may or may not be causal dependence in either direction, or even both directions simultaneously.
We would need know the interface type `B` and possibly the inner
workings of the components to make judgments about causal dependence. In general, processing can take place in `g` even
before any information passes through the `B` interface.

## Parallel composition

Any two components `f`, `g`

```
┏━━━━━━━━━━━━┓
┞─┐          ┞─┐
╎A│    f     ╎C│
┟─┘          ┟─┘
┗━━━━━━━━━━━━┛
┏━━━━━━━━━━━━┓
┞─┐          ┞─┐
╎B│    g     ╎D│
┟─┘          ┟─┘
┗━━━━━━━━━━━━┛
```

can be put alongside each other (parallel to each other) to form their _parallel composition_ _f ⊗ g_

```
┏━━━━━━━━━━━━┓
┞─┐          ┞─┐
╎A│          ╎C│
┟─┘  f ⊗ g   ┟─┘
┞─┐          ┞─┐
╎B│          ╎D│
┟─┘          ┟─┘
┗━━━━━━━━━━━━┛
```

## Scala notation

The graphical notation is useful for a human, but eventually we have to express our Libretto program by means of the
host language, Scala.

A component `f` with one in-port of type `A` and one out-port of type `B`

```
┏━━━━━━━━━━━━┓
┞─┐          ┞─┐
╎A│    f     ╎B│
┟─┘          ┟─┘
┗━━━━━━━━━━━━┛
```

is a value `f` of type `A -⚬ B`.

The funny arrow-like symbol, `-⚬`, also called a _lollipop_, is borrowed from linear logic where it denotes _linear
implication_ and in Libretto we similarly call it a _linear function._ We will also call it simply an _arrow_ if there
is no risk of confusion with other things called arrows. So we use the terms component, linear function and arrow as
synonyms.

☝️ Although we call `-⚬` a linear _function,_ some intuitions one might have about Scala functions (`=>`) do not
transfer to `-⚬`. With a Scala function, there is nothing going on inside it until we pass all the inputs to it.
Once we get the output (and we get the whole output all at once), the Scala function is done. Remember, however,
that Libretto's linear function is a component, a part of the system that runs on its own and perhaps communicates
with its environment through the ports.
However, composition of Libretto's linear functions works just like composition of Scala functions.

In Scala, we model multiple in-ports as a single in-port of a composite type, and similarly for out-ports.
As an example, a component `f` with two in-ports of types `A` and `B` and two out-ports of types `C` and `D`

```
┏━━━━━━━━━━━━┓
┞─┐          ┞─┐
╎A│          ╎C│
┟─┘    f     ┟─┘
┞─┐          ┞─┐
╎B│          ╎D│
┟─┘          ┟─┘
┗━━━━━━━━━━━━┛
```

is represented as a value `f: (A ⊗ B) -⚬ (C ⊗ D)`.
The expression _X ⊗ Y_ represents a **concurrent pair** of _X_ and _Y_, sometimes referred to simply as _X times Y_.
It is also called a _tensor product_ or a _monoidal product_ (of a monoidal category).

Because the ⊗ symbol is usually not very intelligible in monospace fonts (e.g. hardly distinguishable from ⊕, compare
`⊗` vs. `⊕`), in code we usually use `|*|` for the concurrent pair.
The above component is then `f: (A |*| B) -⚬ (C |*| D)`.

The operator for sequential composition introduced above is `andThen` (again, do not assume any temporal meaning):

```scala
def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C
```

There are syntactic extensions that let us write

- `f > g` instead of `andThen(f, g)`,
- `f ⚬ g` (read _f after g_) instead of `andThen(g, f)`.

The operator for parallel composition is `par`:

```scala
def par[A, B, C, D](
  f: A -⚬ B,
  g: C -⚬ D,
): (A |*| C) -⚬ (B |*| D)
```

## Identity

For any type `A` there is an _identity_ function (component)

```scala
/*  ┏━━━━━━━━━━━━┓
 *  ┞─┐          ┞─┐
 *  ╎A│  id[A]   ╎A│
 *  ┟─┘          ┟─┘
 *  ┗━━━━━━━━━━━━┛
 */
def id[A]: A -⚬ A
```

All it does is relay information from in-ports to out-ports and from out-ports to in-ports, unchanged.
It can be thought of as an extension cord. It is not useful by itself, but it comes in handy in compositions.

As an example, say that we want to connect the second out-port of `f: A -⚬ (B |*| C)` to the in-port of
`g: C -⚬ D`. In the graphical notation, it is tempting to just put them next to each other like this:

```
┏━━━━━━━━━━━┓
┃           ┞─┐
┃           ╎B│
┞─┐         ┟─┘
╎A│   f     ┣━━━━━━━━━━━┓
┟─┘         ┞─┐         ┞─┐
┃           ╎C│    g    ╎D│
┃           ┟─┘         ┟─┘
┗━━━━━━━━━━━┻━━━━━━━━━━━┛
```

But how would we do it in Scala using only what we already know, namely sequential and parallel composition?
We can first place `id[B]` parallel to `g`, obtaining

```
                    ┏━━━━━━━━━━━┓
                    ┞─┐         ┞─┐
                    ╎B│  id[B]  ╎B│
                    ┟─┘         ┟─┘
par(id[B], g)   =   ┠╌╌╌╌╌╌╌╌╌╌╌┨
                    ┞─┐         ┞─┐
                    ╎C│    g    ╎D│
                    ┟─┘         ┟─┘
                    ┗━━━━━━━━━━━┛
```

and then place it after `f`, obtaining

```
                        ┏━━━━━━━━━━━┯━━━━━━━━━━━┓
                        ┃           ├─┐         ┞─┐
                        ┃           ╎B│  id[B]  ╎B│
                        ┞─┐         ├─┘         ┟─┘
f > par(id[B], g)   =   ╎A│   f     ├╌╌╌╌╌╌╌╌╌╌╌┨
                        ┟─┘         ├─┐         ┞─┐
                        ┃           ╎C│    g    ╎D│
                        ┃           ├─┘         ┟─┘
                        ┗━━━━━━━━━━━┷━━━━━━━━━━━┛
```

There are shortcuts for transforming just one part of a concrrent pair, like above,
using identity in the other part:

```scala mdoc
/** Applies `f` to the first part of a concurrent pair. */
def fst[A, B, C](f: A -⚬ C): (A |*| B) -⚬ (C |*| B) =
  par(f, id[B])

/** Applies `g` to the second part of a concurrent pair. */
def snd[A, B, C](g: B -⚬ C): (A |*| B) -⚬ (A |*| C) =
  par(id[A], g)
```

## Associativity of ⊗

If we are designing a component with more than two in-ports or out-ports, such as this one,

```
┏━━━━━━━━━━━━┓
┃            ┞─┐
┃            ╎B│
┃            ┟─┘
┞─┐          ┞─┐
╎A│    f     ╎C│
┟─┘          ┟─┘
┃            ┞─┐
┃            ╎D│
┃            ┟─┘
┗━━━━━━━━━━━━┛
```

we need to choose how to group the ports using ⊗ (`|*|`) in the Scala representation.
For the above component, there are two possibilities:

```scala
f1: A -⚬ ((B |*| C) |*| D)
f2: A -⚬ (B |*| (C |*| D))
```

Sometimes one way is more natural than the other, but often it is an arbitrary choice.
We need not worry about it too much, though, because the grouping does not matter:
we can always regroup the ports using

```scala
def assocLR[X, Y, Z]: ((X |*| Y) |*| Z) -⚬ (X |*| (Y |*| Z))
def assocRL[X, Y, Z]: (X |*| (Y |*| Z)) -⚬ ((X |*| Y) |*| Z)
```

```
┏━━━━━━━━━━━━━━━━┓             ┏━━━━━━━━━━━━━━━━┓
┞─┐              ┞─┐           ┞─┐              ┞─┐
╎X│              ╎X│           ╎X│              ╎X│
╎⊗│              ┟─┘           ┟─┘              ╎⊗│
╎Y│   assocLR    ┞─┐           ┞─┐   assocRL    ╎Y│
┟─┘              ╎Y│           ╎Y│              ┟─┘
┞─┐              ╎⊗│           ╎⊗│              ┞─┐
╎Z│              ╎Z│           ╎Z│              ╎Z│
┟─┘              ┟─┘           ┟─┘              ┟─┘
┗━━━━━━━━━━━━━━━━┛             ┗━━━━━━━━━━━━━━━━┛
```

Thus, if we have

```scala mdoc
def f1: A -⚬ ((B |*| C) |*| D) =
  ???
```

we can always get

```scala mdoc:compile-only
def f2: A -⚬ (B |*| (C |*| D)) =
  f1 > assocLR
```

## Symmetry of ⊗

The relative order of ports does not matter, either.

If, for example, we have a component

```scala mdoc
/*  ┏━━━━━━━━━━━━━━━━┓
 *  ┞─┐              ┞─┐
 *  ╎A│              ╎C│
 *  ┟─┘              ┟─┘
 *  ┃       g1       ┞─┐
 *  ┃                ╎D│
 *  ┞─┐              ╎⊗│
 *  ╎B│              ╎E│
 *  ┟─┘              ┟─┘
 *  ┗━━━━━━━━━━━━━━━━┛
 *
 */
def g1: (A |*| B) -⚬ (C |*| (D |*| E)) =
  ???
```

and need

```scala mdoc:compile-only
def g2: (B |*| A) -⚬ ((E |*| D) |*| C) =
  ???
```

we can "easily" get it using `swap`

```scala
/*  ┏━━━━━━━━━━━━━━━━┓
 *  ┞─┐              ┞─┐
 *  ╎X│              ╎Y│
 *  ┟─┘  swap[X,Y]   ┟─┘
 *  ┞─┐              ┞─┐
 *  ╎Y│              ╎X│
 *  ┟─┘              ┟─┘
 *  ┗━━━━━━━━━━━━━━━━┛
 *
 */
def swap[X, Y]: (X |*| Y) -⚬ (Y |*| X)
```

like this

```scala mdoc:compile-only
/*  ┏━━━━━━━━━━━━┯━━━━━━━━━━━━━━━━┯━━━━━━━━━━━━━━━━┯━━━━━━━━━━━━━━━┓
 *  ┞─┐          ├─┐              ├─┐              ├─┐             ┞─┐
 *  ╎B│          ╎A│              ╎C│              ╎D│             ╎E│
 *  ┟─┘          ├─┘              ├─┘              ╎⊗│  swap[D, E] ╎⊗│
 *  ┃            ╎                ╎ swap[C, D ⊗ E] ╎E│             ╎D│
 *  ┃ swap[B, A] ╎       g1       ├─┐              ├─┘             ┟─┘
 *  ┃            ╎                ╎D│              ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┨
 *  ┞─┐          ├─┐              ╎⊗│              ├─┐             ┞─┐
 *  ╎A│          ╎B│              ╎E│              ╎C│    id[C]    ╎C│
 *  ┟─┘          ├─┘              ├─┘              ├─┘             ┟─┘
 *  ┗━━━━━━━━━━━━┷━━━━━━━━━━━━━━━━┷━━━━━━━━━━━━━━━━┷━━━━━━━━━━━━━━━┛
 */
val g2: (B |*| A) -⚬ ((E |*| D) |*| C) =
  swap[B, A] > g1 > swap[C, D |*| E] > par(swap[D, E], id[C])
```

Okay, that was a lot of glue code to wrap around the function `g1`.
Having to explicitly put in the glue code can be quite distracting from what is going on.
Let's just foreshadow here that alternatively, we can use λ-syntax,
which generates the glue code automatically:

```scala mdoc:compile-only
val g2: (B |*| A) -⚬ ((E |*| D) |*| C) =
  λ { case (b |*| a) =>
    val (c |*| (d |*| e)) = g1(a |*| b)
    (e |*| d) |*| c
  }
```

More on λ-syntax later.

## The no-flow port, `One`

Sometimes we want a component with no in-ports or no out-ports, such as these ones

```
┏━━━━━━━━━━━━┓            ┏━━━━━━━━━━━━┓
┃            ┞─┐          ┞─┐          ┃
┃      f     ╎A│          ╎B│    g     ┃
┃            ┟─┘          ┟─┘          ┃
┗━━━━━━━━━━━━┛            ┗━━━━━━━━━━━━┛
```

In Scala representation, however, we have to specify the type of in-port and the type of outport.
There is a special fake port type, `One`, through which there is no flow of information in either direction.

We can declare the above two components as

```scala
val f: One -⚬ A
val g: B -⚬ One
```

In graphical notation, we omit `One`-typed ports if they do not add any value (such as above), but keep them if they do
(such as below).

We can freely add and remove `One` to/from in-ports and/or out-ports using the following primitives:

```scala
//  ┏━━━━━━━━━━━━━┓           ┏━━━━━━━━━━━━━━━━┓
//  ┃             ┞───┐       ┞───┐            ┃
//  ┃             ╎One│       ╎One│            ┃
//  ┃ introFst[A] ┟───┘       ┟───┘ elimFst[A] ┃
//  ┞───┐         ┞───┐       ┞───┐            ┞───┐
//  ╎ A │         ╎ A │       ╎ A │            ╎ A │
//  ┟───┘         ┟───┘       ┟───┘            ┟───┘
//  ┗━━━━━━━━━━━━━┛           ┗━━━━━━━━━━━━━━━━┛
//
//  ┏━━━━━━━━━━━━━┓           ┏━━━━━━━━━━━━━━━━┓
//  ┞───┐         ┞───┐       ┞───┐            ┞───┐
//  ╎ A │         ╎ A │       ╎ A │            ╎ A │
//  ┟───┘         ┟───┘       ┟───┘            ┟───┘
//  ┃ introSnd[A] ┞───┐       ┞───┐ elimSnd[A] ┃
//  ┃             ╎One│       ╎One│            ┃
//  ┃             ┟───┘       ┟───┘            ┃
//  ┗━━━━━━━━━━━━━┛           ┗━━━━━━━━━━━━━━━━┛

def introFst[A]: A -⚬ (One |*| A)
def introSnd[A]: A -⚬ (A |*| One)
def elimFst[A]: (One |*| A) -⚬ A
def elimSnd[A]: (A |*| One) -⚬ A
```

Soon we are going to see useful cases of adding and removing `One`s.

Since there is no flow of information through `One`, there is also _no causal dependency through `One`-typed ports._
This means, for example, that in

```
┏━━━━━━━━━┯━━━━━━━━━━━━━┯━━━━━━━━━━━┓
┃         ╎             ├───┐       ┞───┐
┃         ╎             ╎One│   g   ╎ B │
┃         ╎             ├───┘       ┟───┘
┃    f    ╎ introFst[C] ├╌╌╌╌╌╌╌╌╌╌╌┨
┞───┐     ├───┐         ├───┐       ┞───┐
╎ A │     ╎ C │         ╎ C │ id[C] ╎ C │
┟───┘     ├───┘         ├───┘       ┟───┘
┗━━━━━━━━━┷━━━━━━━━━━━━━┷━━━━━━━━━━━┛
```

there is no causal dependence of `g` on anything in `f` going through the `introFst[C]` component.

## Signals

By a signal we mean a notification that some event has occurred. The signal itself carries no information about the
event, though, it only signals that the event has occurred.

There are 4 types of signals, differing in the direction of travel and/or whether they can be dismissed:

|                          | Non-dismissible | Dismissible |
| ------------------------ | --------------- | ----------- |
| Positive (left-to-right) |     `Done`      |   `Ping`    |
| Negative (right-to-left) |     `Need`      |   `Pong`    |

- Positive signals (`Done`, `Ping`) travel in the direction of `-⚬`.
- Negative signals (`Need`, `Pong`) travel in the direction opposite to `-⚬`.

Signals are useful for creating causal dependencies: one component might wait for a signal from another component
before proceeding with further processing. For example, the signal might signal completion of a request and further
processing might be accepting another request, effectively sequencing request processing.

For someone used to `Future` and `Promise`, it might be helpful, _despite important differences,_ to initially view

- `Done` and `Ping` as `Future[Unit]`,
- `Need` and `Pong` as `Promise[Unit]`.

### Immediate signals

There are primitive components that fire a signal immediately. More precisely, as soon as it is certain that
they will be executed (but we haven't seen any conditional operators yet). These are

```scala
//  ┏━━━━━━━━━━━━┓         ┏━━━━━━━━━━━━━━┓     ┏━━━━━━━━━━━━┓         ┏━━━━━━━━━━━━━━┓
//  ┃            ┞────┐    ┞────┐         ┃     ┃            ┞────┐    ┞────┐         ┃
//  ┃    done    ╎Done│    ╎Need│  need   ┃     ┃    ping    ╎Ping│    ╎Pong│  pong   ┃
//  ┃            ┟────┘    ┟────┘         ┃     ┃            ┟────┘    ┟────┘         ┃
//  ┗━━━━━━━━━━━━┛         ┗━━━━━━━━━━━━━━┛     ┗━━━━━━━━━━━━┛         ┗━━━━━━━━━━━━━━┛

def done: One -⚬ Done
def need: Need -⚬ One
def ping: One -⚬ Ping
def pong: Pong -⚬ One
```

### Non-dismissible signals

`Done` and `Need` are non-dismissible: once created, they have to be used
(typically as a trigger for another action).
In this way, an incoming non-dismissible signal, whether `Done` incoming from the left
or `Need` incoming from the right, is a liability.

`Done` and `Need` are used to transfer the obligation to wait for a running task.
Ignoring such a signal would mean losing track of the running task, which is a resource leak,
and thus is prohibited.

### Dismissible signals

`Ping` and `Pong` are used to signal completion of a task, but do not transfer the obligation
to await that task, because someone else is already keeping track of it.

The receiver of `Ping` or `Pong` may ignore the signal using

```scala
def dismissPing: Ping -⚬ One
def dismissPong: One -⚬ Pong
```

### Forking and joining signals

_Forking_ a signal means that as soon as the signal arrives, two new signals are fired.

```scala
//  ┏━━━━━━━━━━┓         ┏━━━━━━━━━━┓         ┏━━━━━━━━━━┓         ┏━━━━━━━━━━┓
//  ┃   fork   ┞────┐    ┃ forkPing ┞────┐    ┞────┐     ┃         ┞────┐     ┃
//  ┃          ╎Done│    ┃          ╎Ping│    ╎Need│     ┃         ╎Pong│     ┃
//  ┞────┐     ┟────┘    ┞────┐     ┟────┘    ┟────┘     ┞────┐    ┟────┘     ┞────┐
//  ╎Done│     ┃         ╎Ping│     ┃         ┃ forkNeed ╎Need│    ┃ forkPong ╎Pong│
//  ┟────┘     ┞────┐    ┟────┘     ┞────┐    ┞────┐     ┟────┘    ┞────┐     ┟────┘
//  ┃          ╎Done│    ┃          ╎Ping│    ╎Need│     ┃         ╎Pong│     ┃
//  ┃          ┟────┘    ┃          ┟────┘    ┟────┘     ┃         ┟────┘     ┃
//  ┗━━━━━━━━━━┛         ┗━━━━━━━━━━┛         ┗━━━━━━━━━━┛         ┗━━━━━━━━━━┛

def fork     : Done -⚬ (Done |*| Done)
def forkPing : Ping -⚬ (Ping |*| Ping)
def forkNeed : (Need |*| Need) -⚬ Need
def forkPong : (Pong |*| Pong) -⚬ Pong
```

Remember that `Need` and `Pong` travel from right to left, so `forkNeed` and `forkPong` have
one signal coming in from the right and two signals coming out on the left.

_Joining_ two signals means to fire a signal as soon as both signals arrive.

```scala
//  ┏━━━━━━━━━━┓         ┏━━━━━━━━━━┓         ┏━━━━━━━━━━┓         ┏━━━━━━━━━━┓
//  ┞────┐     ┃         ┞────┐     ┃         ┃ joinNeed ┞────┐    ┃ joinPong ┞────┐
//  ╎Done│     ┃         ╎Ping│     ┃         ┃          ╎Need│    ┃          ╎Pong│
//  ┟────┘     ┞────┐    ┟────┘     ┞────┐    ┞────┐     ┟────┘    ┞────┐     ┟────┘
//  ┃   join   ╎Done│    ┃ joinPing ╎Ping│    ╎Need│     ┃         ╎Pong│     ┃
//  ┞────┐     ┟────┘    ┞────┐     ┟────┘    ┟────┘     ┞────┐    ┟────┘     ┞────┐
//  ╎Done│     ┃         ╎Ping│     ┃         ┃          ╎Need│    ┃          ╎Pong│
//  ┟────┘     ┃         ┟────┘     ┃         ┃          ┟────┘    ┃          ┟────┘
//  ┗━━━━━━━━━━┛         ┗━━━━━━━━━━┛         ┗━━━━━━━━━━┛         ┗━━━━━━━━━━┛

def join     : (Done |*| Done) -⚬ Done
def joinPing : (Ping |*| Ping) -⚬ Ping
def joinNeed : Need -⚬ (Need |*| Need)
def joinPong : Pong -⚬ (Pong |*| Pong)
```

Again, since `Need` and `Pong` travel from right to left, `joinNeed` and `joinPong` have
two signals coming in from the right and one signal coming out on the left

### Inverting signals

There are primitives to invert the direction of a signal.

A signal traveling to the left (`Need`, `Pong`) can be changed to the respective signal traveling to the right (`Done`, `Ping`).

A signal traveling to the right (`Done`, `Ping`) can be changed to the respective signal traveling to the left (`Need`, `Pong`).

```scala
//  lInvertSignal           rInvertSignal      lInvertPongPing        rInvertPingPong
//  ┏━━━━━━━━━━┓             ┏━━━━━━━━━━┓      ┏━━━━━━━━━━┓             ┏━━━━━━━━━━┓
//  ┃          ┃             ┃          ┃      ┃          ┃             ┃          ┃
//  ┃          ┞────┐        ┞────┐     ┃      ┃          ┞────┐        ┞────┐     ┃
//  ┃       ┌┄┄╎Need│←┄    ┄→╎Done│┄┄┐  ┃      ┃       ┌┄┄╎Pong│←┄    ┄→╎Ping│┄┄┐  ┃
//  ┃       ┆  ┟────┘        ┟────┘  ┆  ┃      ┃       ┆  ┟────┘        ┟────┘  ┆  ┃
//  ┃       ┆  ┃             ┃       ┆  ┃      ┃       ┆  ┃             ┃       ┆  ┃
//  ┃       ┆  ┞────┐        ┞────┐  ┆  ┃      ┃       ┆  ┞────┐        ┞────┐  ┆  ┃
//  ┃       └┄→╎Done│┄→    ←┄╎Need│←┄┘  ┃      ┃       └┄→╎Ping│┄→    ←┄╎Pong│←┄┘  ┃
//  ┃          ┟────┘        ┟────┘     ┃      ┃          ┟────┘        ┟────┘     ┃
//  ┗━━━━━━━━━━┛             ┗━━━━━━━━━━┛      ┗━━━━━━━━━━┛             ┗━━━━━━━━━━┛


def lInvertSignal   : One -⚬ (Need |*| Done)
def rInvertSignal   : (Done |*| Need) -⚬ One
def rInvertPingPong : (Ping |*| Pong) -⚬ One
def lInvertPongPing : One -⚬ (Pong |*| Ping)
```

Using these, we can always move a signal to the other side of the `-⚬` arrow while changing its direction.
For example, given

```scala mdoc
/*  ┏━━━━━━━━━━━━┓
 *  ┞────┐       ┃
 *  ╎Done│       ┃
 *  ┟────┘   f   ┃
 *  ┞────┐       ┞────┐
 *  ╎ A  │       ╎ B  │
 *  ┟────┘       ┟────┘
 *  ┗━━━━━━━━━━━━┛
 */
def f: (Done |*| A) -⚬ B =
  ???
```

we can always obtain

```scala mdoc:compile-only
/*  ┏━━━━━━━━━━━━━┓
 *  ┃             ┞────┐
 *  ┃             ╎Need│
 *  ┃       g     ┟────┘
 *  ┞────┐        ┞────┐
 *  ╎ A  │        ╎ B  │
 *  ┟────┘        ┟────┘
 *  ┗━━━━━━━━━━━━━┛
 */
def g: A -⚬ (Need |*| B) =
  ???
```

roughly like this

```
┏━━━━━━━━━━━━━━━┯━━━━━━━━━━━━━━━┓
┃ lInvertSignal ├────┐ id[Need] ┞────┐
┃          ┌┄┄┄┄╎Need│←┄┄┄┄┄┄┄┄┄╎Need│←┄
┃          ┆    ├────┘          ┟────┘
┃          ┆    ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┨
┃          ┆    ├────┐          ┃
┃          └┄┄┄→╎Done│          ┃
┃               ├────┘          ┃
┠╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┤       f       ┃
┞───┐           ├───┐           ┞───┐
╎ A │   id[A]   ╎ A │           ╎ B │
┟───┘           ├───┘           ┟───┘
┗━━━━━━━━━━━━━━━┷━━━━━━━━━━━━━━━┛
```

and precisely (including all the necessary glue) like this

```scala mdoc
/*  ┏━━━━━━━━━━━━━┯━━━━━━━━━━━━━━━┯━━━━━━━━━━━━━━┯━━━━━━━━━━━━━━━┓
 *  ┃             ╎ lInvertSignal ├────┐         ├────┐          ┞────┐
 *  ┃ introFst[A] ├───┐           ╎Need│         ╎Need│ id[Need] ╎Need│
 *  ┃             ╎One│           ╎ ⊗  │         ├────┘          ┟────┘
 *  ┃             ├───┘           ╎Done│         ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┨
 *  ┃             ╎               ├────┘         ├────┐          ┃
 *  ┃             ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┤    assocLR   ╎Done│          ┃
 *  ┞───┐         ├───┐           ├───┐          ╎ ⊗  │    f     ┞───┐
 *  ╎ A │         ╎ A │   id[A]   ╎ A │          ╎ A  │          ╎ B │
 *  ┟───┘         ├───┘           ├───┘          ├────┘          ┟───┘
 *  ┗━━━━━━━━━━━━━┷━━━━━━━━━━━━━━━┷━━━━━━━━━━━━━━┷━━━━━━━━━━━━━━━┛
 */
def g: A -⚬ (Need |*| B) =
  introFst[A] > par(lInvertSignal, id[A]) > assocLR > par(id[Need], f)
```

We can also use λ-syntax:

```scala mdoc:compile-only
def g: A -⚬ (Need |*| B) =
  λ { a =>
    val (a1 |*| (need |*| done)) =
      a also lInvertSignal
    need |*| f(done |*| a1)
  }
```

## Either (⊕)

Type `A ⊕ B` (in code we use `A |+| B` for easier typing and better intelligibility) means either `A` or `B` (but
not both), and which one it is going to be is decided by the component on the left.
In other words, a component that has `A ⊕ B` as an out-port decides whether the interaction will continue as `A` or
as `B`, while a component that has `A ⊕ B` as an in-port has to be able to handle either case.
That is, the decision flows from left to right (the positive direction).

Primitives for making the decision (introducing `|+|`) are

```scala
//  ┏━━━━━━━━━━━━━━┓               ┏━━━━━━━━━━━━━━┓
//  ┞───┐          ┞───┐           ┃              ┞───┐
//  ╎ A │          ╎ A │           ┃ injectR[A,B] ╎ A │
//  ┟───┘          ╎ ⊕ │           ┞───┐          ╎ ⊕ │
//  ┃ injectL[A,B] ╎ B │           ╎ B │          ╎ B │
//  ┃              ┟───┘           ┟───┘          ┟───┘
//  ┗━━━━━━━━━━━━━━┛               ┗━━━━━━━━━━━━━━┛

def injectL[A, B]: A -⚬ (A |+| B)
def injectR[A, B]: B -⚬ (A |+| B)
```

These are analogous to Scala's `Left(a)` and `Right(b)` constructors of `Either[A, B]`.

The primitive for handling the actually chosen side (eliminating `|+|`) is

```scala
/**  ┏━━━━━━━━━━━━━━┓
  *  ┞───┬──────────┨
  *  ╎ A ╷    f     ┞───┐
  *  ╎ ⊕ ├──────────╎ C │
  *  ╎ B ╵    g     ┟───┘
  *  ┟───┴──────────┨
  *  ┗━━━━━━━━━━━━━━┛
  */
def either[A, B, C](f: A -⚬ C, g: B -⚬ C): (A |+| B) -⚬ C
```

It is analogous to Scala's `Either#fold(f: A => C, g: B => C): C`.

Once it is decided which case it is going to be, the corresponding component, `f` or `g`, is executed:

```
  ┏━━━━━━━━━━━━━━┓                          ┏━━━━━━━━━━━━━━┓
  ┞───┬────────╮ ┃                          ┞───┐          ┃
  ╎*A*╎   f    ╰─╀───┐                      ╎ A │     ╭────╀───┐
  ╎ ⊕ ├─────╮    ╎ C │                      ╎ ⊕ ├─────╯    ╎ C │
  ╎ B │     ╰────╁───┘                      ╎*B*╎   g    ╭─╁───┘
  ┟───┘          ┃                          ┟───┴────────╯ ┃
  ┗━━━━━━━━━━━━━━┛                          ┗━━━━━━━━━━━━━━┛
```

☝️ Note, however, that in `either(f > h, g > h)`, the common part, `h`, is certain to be executed in either case,
and thus may start executing even before the `|+|` is decided. Indeed, it must hold that

```scala
either(f > h, g > h) = either(f, g) > h
```

## Choice (&)

Type `A & B` (we use `A |&| B` in code to avoid confusion with the bitwise and operator in Scala, and for consistency
with `|*|` and `|+|`) means an _exclusive_ choice between `A` and `B`.
The component to the right of `A & B`, i.e. the one that has `A & B` as an in-port, gets to choose whether
the interaction with the component to the left will continue as `A` or as `B`.
The component to the left of `A & B`, i.e. the one that has `A & B` as an out-port, has to be able to provide
either of them (but not both of them simultaneously).
That is, the decision flows from right to left (the negative direction).

Primitives for choosing one of the options (eliminating `|&|`) are

```scala
//  ┏━━━━━━━━━━━━━━━━━━┓               ┏━━━━━━━━━━━━━━━━━━┓
//  ┞───┐              ┞───┐           ┞───┐              ┃
//  ╎ A │              ╎ A │           ╎ A │              ┃
//  ╎ & │ chooseL[A,B] ┟───┘           ╎ & │ chooseR[A,B] ┞───┐
//  ╎ B │              ┃               ╎ B │              ╎ B │
//  ┟───┘              ┃               ┟───┘              ┟───┘
//  ┗━━━━━━━━━━━━━━━━━━┛               ┗━━━━━━━━━━━━━━━━━━┛

def chooseL[A, B]: (A |&| B) -⚬ A
def chooseR[A, B]: (A |&| B) -⚬ B
```

They are somewhat analogous to `_1`, `_2` methods on Scala's 2-tuple, except as if by using `_1` you give up the chance
to ever access `_2`, and vice versa.

The primitive for offering a choice (introducing `|&|`) is

```scala
/**  ┏━━━━━━━━━━━━━━┓
  *  ┃   ┌──────────╀───┐
  *  ┞───┤    f     ╷ B │
  *  ╎ A ├──────────┤ & │
  *  ┟───┤    g     ╵ C │
  *  ┃   └──────────┟───┘
  *  ┗━━━━━━━━━━━━━━┛
  */
def choice[A, B, C](f: A -⚬ B, g: A -⚬ C): A -⚬ (B |&| C)
```

Once the choice is made from the right, the corresponding component, `f` or `g`, is executed:

```
  ┏━━━━━━━━━━━━━━┓                      ┏━━━━━━━━━━━━━━┓
  ┃     ╭────────╀───┐                  ┃              ┞───┐
  ┞───┬─╯   f    ╎*B*│                  ┞───┬─────╮    ╎ B │
  ╎ A ╎    ╭─────┤ & │                  ╎ A ╎     ╰────┤ & │
  ┟───┴────╯     │ C │                  ┟───┴─╮   g    │*C*│
  ┃              ┟───┘                  ┃     ╰────────╁───┘
  ┗━━━━━━━━━━━━━━┛                      ┗━━━━━━━━━━━━━━┛
```

☝️ Note, however, that in `choice(h > f, h > g)`, the common part, `h`, is certain to be executed in either case,
and thus may start executing even before the `|&|` is decided. Indeed, it must hold that

```scala
choice(h > f, h > g) = h > choice(f, g)
```

## Distributivity of ⊗ over ⊕

The tensor product ⊗ distributes over ⊕:

```scala
//  ┏━━━━━━━━━━━━━━━━┓                        ┏━━━━━━━━━━━━━━━━┓
//  ┞─┐              ┞───┐                    ┞─┐              ┞───┐
//  ╎A│              ╎⎛A⎞│                    ╎A│              ╎⎛A⎞│
//  ┟─┘              ╎⎜⊗⎟│                    ╎⊕│              ╎⎜⊗⎟│
//  ┃                ╎⎝B⎠│                    ╎B│              ╎⎝C⎠│
//  ┞─┐ distributeL  ╎ ⊕ │                    ┟─┘ distributeR  ╎ ⊕ │
//  ╎B│              ╎⎛A⎞│                    ┃                ╎⎛B⎞│
//  ╎⊕│              ╎⎜⊗⎟│                    ┞─┐              ╎⎜⊗⎟│
//  ╎C│              ╎⎝C⎠│                    ╎C│              ╎⎝C⎠│
//  ┟─┘              ┟───┘                    ┟─┘              ┟───┘
//  ┗━━━━━━━━━━━━━━━━┛                        ┗━━━━━━━━━━━━━━━━┛

def distributeL[A, B, C]: (A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C))
def distributeR[A, B, C]: ((A |+| B) |*| C) -⚬ ((A |*| C) |+| (B |*| C))
```

These are primitives (actually, one of them is sufficient thanks to symmetry of ⊗).
Note that arrows in the opposite direction need not be primitives, as they are always available:

```scala
def factorL[A, B, C]: ((A |*| B) |+| (A |*| C)) -⚬ (A |*| (B |+| C)) =
  either(par(id, injectL), par(id, injectR))

def factorR[A, B, C]: ((A |*| C) |+| (B |*| C)) -⚬ ((A |+| B) |*| C) =
  either(par(injectL, id), par(injectR, id))
```

## Co-distributivity of ⊗ over &

The tensor product ⊗ distributes over & as well, only in the opposite (right-to-left) direction.
This is consistent with the choice being made on the right of `A |&| B` and being propagated to the left.
It is therefore helpful to read the following components from right to left to see how one out-port is being distributed
over the choice in the other out-port.

```scala
//  ┏━━━━━━━━━━━━━━━━━━━┓                        ┏━━━━━━━━━━━━━━━━━━━┓
//  ┞───┐               ┞─┐                      ┞───┐               ┞─┐
//  ╎⎛A⎞│               ╎A│                      ╎⎛A⎞│               ╎A│
//  ╎⎜⊗⎟│               ┟─┘                      ╎⎜⊗⎟│               ╎&│
//  ╎⎝B⎠│               ┃                        ╎⎝C⎠│               ╎B│
//  ╎ & │ coDistributeL ┞─┐                      ╎ & │ coDistributeR ┟─┘
//  ╎⎛A⎞│               ╎B│                      ╎⎛B⎞│               ┃
//  ╎⎜⊗⎟│               ╎&│                      ╎⎜⊗⎟│               ┞─┐
//  ╎⎝C⎠│               ╎C│                      ╎⎝C⎠│               ╎C│
//  ┟───┘               ┟─┘                      ┟───┘               ┟─┘
//  ┗━━━━━━━━━━━━━━━━━━━┛                        ┗━━━━━━━━━━━━━━━━━━━┛

def coDistributeL[A, B, C]: ((A |*| B) |&| (A |*| C)) -⚬ (A |*| (B |&| C))
def coDistributeR[A, B, C]: ((A |*| C) |&| (B |*| C)) -⚬ ((A |&| B) |*| C)
```

The intuition behind `coDistributeL` above is this: Only after the choice between `B` and `C` is made (from the right)
is it decided how the `A` on the other out-port is produced, namely, whether it is the `A` from `A ⊗ B` or the `A` from
`A ⊗ C`.

At least one of these needs to be a primitive (the other one can be obtained thanks to symmetry of ⊗).
Note that arrows in the opposite direction need not be primitives, as they are always available:

```scala mdoc
def coFactorL[A, B, C]: (A |*| (B |&| C)) -⚬ ((A |*| B) |&| (A |*| C)) =
  choice(par(id, chooseL), par(id, chooseR))

def coFactorR[A, B, C]: ((A |&| B) |*| C) -⚬ ((A |*| C) |&| (B |*| C)) =
  choice(par(chooseL, id), par(chooseR, id))
```

## Linearity and point-free style

When composing components into larger components, it would be undesirable if somewhere inside a composite component
some ports remained unconnected or accidentally connected multiple times.

The property of each port being connected exactly once is called _linearity_—data and resources flow through the system
in a linear fashion, without being duplicated or ignored (except via explicit operators for precisely that purpose).

_In Libretto, linearity is ensured by construction._
Data types used to represent Libretto programs are simply unable to represent non-linear programs.
Notice how in composition operations, each port of a sub-program either is connected (and thus absent
from the resulting program's interface) or becomes a port of the resulting composite program.

Notice how the way we have been composing Libretto programs so far is like composing Scala functions in _point-free style,_
i.e. when one defines functions by composing smaller functions, without ever referring to the function's input variables.
For a moment, forget the differences between `-⚬` and `=>` and view in-ports as function inputs.
In Libretto, we define the (linear) function without ever having access to the inputs as Scala values.
Indeed, user code will never have access to values of types like `One`, `Done`, `Need`, `A |*| B`, `A |+| B`, `A & B`
or others that we will encounter later<sup>(*)</sup>. If it did, it would break linearity,
because Scala functions can freely ignore or duplicate (references to) values.

_Using point-free composition guarantees linearity at compile-time._

<sup>(*)</sup> Moreover, not only are values of the above types not accessible to a user, the types themselves may be uninhabited.
Indeed, they are all uninhabited in the proof-of-concept implementation. This should not be
surprising when you realize that Libretto's linear functions are mere blueprints. What then flows in a running system
when the blueprint is executed need not be values of the auxiliary formal types used in blueprints.

## λ-Syntax

Although point-free composition has the desirable property of ensuring linearity at compile-time,
it can be quite cumbersome. It takes a lot of effort to just say which out-port should be connected
to which in-port.

That is something that would be easier in a point-full style: just name the ports and "pass"
them to functions to obtain new ports. No explicit `swap`s or re-associations that obscure the essence
of the program. That is what _lambda expressions_ are for.

Let's illustrate lambda expressions on an example.

Suppose we want to implement a function `reorg` that just reorganizes its in-ports:

```scala mdoc:compile-only
val reorg: ((A |*| B) |*| (C |*| D)) -⚬ (((C |*| A) |*| D) |*| B) =
  ???
```

For comparison, let's first do it in point-free style:

```scala mdoc:compile-only
val reorg: ((A |*| B) |*| (C |*| D)) -⚬ (((C |*| A) |*| D) |*| B) =
  fst(swap) > assocLR > swap > fst(assocRL > fst(swap))
```

Well, it is a one-liner, but it is not immediately clear what it does.

Let's now use a λ-expression instead:

```scala mdoc:compile-only
val reorg: ((A |*| B) |*| (C |*| D)) -⚬ (((C |*| A) |*| D) |*| B) =
  λ { case ((a |*| b) |*| (c |*| d)) => (((c |*| a) |*| d) |*| b) }
```

Opinions may vary, but I would say the λ version is more readable.

### How it works

But what is going on here? A moment ago we said that we don't ever access inputs
of a Libretto function as Scala values, yet here we construct a Libretto function

```scala
((A |*| B) |*| (C |*| D)) -⚬ (((C |*| A) |*| D) |*| B)
```

from a Scala function

```scala
{ case ((a |*| b) |*| (c |*| d)) => (((c |*| a) |*| d) |*| b) }
```

Let's look at the type signature of `λ`:

```scala
def λ[A, B](f: $[A] => $[B]): A -⚬ B
```

Indeed, it takes a Scala function and returns a Libretto function.
Notice, however, that to create a Libretto function `A -⚬ B`,
it takes a Scala function `$[A] => $[B]`. In particular, the Scala function
does not have access to a value of type `A`. It has access to `$[A]`, which
is an auxiliary type that exists at the meta level only.

The programmer's task is to construct an expression of type `$[B]` from an expression of type `$[A]`.
The implementation of `λ` then analyzes the resulting `$[B]` expression (which contains occurrences
of the input variable `$[A]`) and infers a (point-free) Libretto function `A -⚬ B`.

### Operations on $-expressions

```scala mdoc:compile-only
// given
val f: A -⚬ C   = ???
val g: One -⚬ D = ???
val h: B -⚬ One = ???

λ { (ab: $[A |*| B]) =>
  // unpair
  val ((a: $[A]) |*| (b: $[B])) = ab

  // pair again
  val ab1: $[A |*| B] = a |*| b

  // pass expression `a` to Libretto function `f`
  val c1: $[C] = a > f
  // or equivalently, apply Libretto function `f` to expression `a`
  val c2: $[C] = f(a)

  val ((a2: $[A]) |*| (d: $[D])) =
    // `one: $[One]` is a constant expression (i.e. not built from other expressions)
    // that can be used as an argument to functions taking `One`, such as `g`
    a |*| g(one)
    // Without `one`, we could equivalently write
    a also g
    // which is a shortcut for
    a > introSnd > snd(g)

  // `alsoElim` is shortcut for eliminating `$[One]`
  val a3: $[A] = a alsoElim h(b)
  // equivalent to
  (a |*| h(b)) > elimSnd
}
```

### Linearity checking

The Scala function `$[A] => $[B]` passed to `λ` is not guaranteed to be linear,
i.e. it may use some part of input more than once or not at all.

Remember that a Libretto function `A -⚬ B` can represent only linear functions.
If a non-linear Scala function is passed to `λ`, it throws an error.
Notice that this error is thrown at assembly time, i.e. when constructing
the Libretto program, in particular, _before_ running the Libretto program.

```scala mdoc:nest:crash
val overusedInput: A -⚬ (A |*| A) =
  λ { a => a |*| a }
```

```scala mdoc:nest:crash
val unusedInput: (A |*| B) -⚬ A =
  λ { case (a |*| b) => a }
```

It is trivial to do linearity checking of programs constructed using λ-expressions in tests.
The test just needs to assemble the program without throwing an exception.

If this is the main program

```scala mdoc
object MyApp {
  import scala.concurrent.duration._

  val prg: Done -⚬ Done =
    λ { start =>
      // some complex program composed of many sub-programs
      start > delay(1.hour)
    }
}
```

then in tests it is sufficient to just access the `val` holding the program to check that
it can be successfully constructed.

```scala mdoc:compile-only
MyApp.prg
```

If the program is constructed at all, it will not throw a linearity error at runtime.

## Recursion

### Recursive types

To define recursive port-types, there is `Rec[F[_]]` type constructor provided as a primitive:

```scala
type Rec[F[_]]

/** Hides one level of a recursive type definition. */
def pack[F[_]]: F[Rec[F]] -⚬ Rec[F]

/** Unpacks one level of a recursive type definition. */
def unpack[F[_]]: Rec[F] -⚬ F[Rec[F]]
```

(Note that `Rec` is analogous to the [Fix](https://hackage.haskell.org/package/data-fix-0.3.1/docs/Data-Fix.html) type
constructor.)

You can roughly think of the abstract type `Rec[F[_]]` as if it was a recursive type alias `type Rec[F[_]] = F[Rec[F]]`.
We just have to do the substitution in either direction explicitly via `pack` and `unpack`.

As an example, let's define a `List` type:

```scala mdoc
//         +-------- element type
//         |    +--- marks occurrences of recursive substructure(s), in this case the tail sub-list
//         |    |     +-- nil     +-- cons
//         |    |     | head --+  |   +-- tail
//         |    |     |        |  |   |
//         V    V     V        V  V   V
type ListF[A, Self] = One |+| (A |*| Self)
type List[A] = Rec[ListF[A, *]] // the * is kind-projector syntax for type lambdas,
                                // in Scala 3 enabled by the -Ykind-projector compiler option.
                                // ListF[A, *] is a shorthand for `X =>> ListF[A, X]`
```

and the `nil` and `cons` constructors:

```scala mdoc
object List {
  def nil[A]: One -⚬ List[A] =
    injectL > pack[ListF[A, *]]

  //     head --+       +-- tail
  //            |       |
  //            V       V
  def cons[A]: (A |*| List[A]) -⚬ List[A] =
    injectR > pack[ListF[A, *]]
}
```

Notes:

- Such a `List` may be produced gradually. For example, one may use the `cons` constructor where the tail is not yet
   known to be either empty or non-empty. Consequently, the head of a list can already be accessed and consumed (e.g.
   by the `map` function defined below) while the tail is still being constructed.
   This is different from `scala.List` where in `val xs = head :: tail` the `tail` is fully constructed before `xs`
   is constructed and its head made accessible for further processing.
- Consequently, `List`s may be infinite and it is not a problem if the elements are consumed at a faster rate than
   they are produced.
- Note that unlike infinite lazy lists in Haskell, the construction of further elements is driven by the `List`
   producer, not by the `List` consumer.

### Recursive functions

To work with recursive structures we need recursive functions.

The general recipe for handling a recursive type `Rec[F]` is

1. "Pretend" we already know how to handle the nested `Rec[F]` substructure(s).
2. Unpack one level of the recursive definition to obtain `F[Rec[F]`.
3. Write code to handle `F[Rec[F]]`, using the made up linear function to handle nested occurrences of `Rec[F]`.

The "pretending" is done by taking a linear function as an argument. More concretely, instead of constructing a linear
function `Rec[F] -⚬ B` directly, we write a Scala function `(Rec[F] -⚬ B) => (Rec[F] -⚬ B)` that constructs the desired
linear function given a linear function of the same signature that it can use to handle substructures. Such Scala
function can then be passed to the primitive `rec` function that "ties the loop" and produces the desired linear
function `Rec[F] -⚬ B`:

```scala
def rec[A, B](f: (A -⚬ B) => (A -⚬ B)): A -⚬ B
```

As an example, let's define a linear function that applies a given linear function to each element of a `List`
(defined above).

```scala mdoc:invisible
import List.{nil, cons}
```
```scala mdoc:nest
object List {
  def map[A, B](f: A -⚬ B): List[A] -⚬ List[B] = {
    //                         +-- pretending we already know how to map the tail
    //                         |
    //                         V
    rec[List[A], List[B]] { (mapTail: List[A] -⚬ List[B]) =>
      unpack > either(
        nil[B],
        par(f, mapTail) > cons[B],
      )
    }
  }
}
```

Notes:

- `par(f, mapTail)` maps the head and the tail of the list concurrently.
- The `cons[B]` constructor may execute as soon as the input list is known to be non-empty.
   In particular, it does not wait for `par(f, mapTail)` to finish.

## Racing

Libretto provides functions for testing which of two concurrent signals arrived first.

The two basic racing operations are on dismissible signals, `Ping` and `Pong`:

```scala
def racePair   : (Ping |*| Ping) -⚬ (One |+| One)
def selectPair : (One |&| One) -⚬ (Pong |*| Pong)
```

In `racePair`, the two `Ping` signals from the in-port race against each other.
If the first signal wins, the output will be left.
If the second signal wins, the output will be right.

In `selectPair`, the two `Pong` signals from the _out_-port race against each other.
If the first signal wins, left will be chosen from the input.
If the second signal wins, right will be chosen from the input.

In both cases, both signals are consumed: the winning one has fired, the slower one is dismissed.

Only one of these operations needs to be a primitive, the other one is derivable using signal inversions discussed above.

There are also versions for non-dismissible signals (`Done` and `Need`):

```scala
def raceDone   : (Done |*| Done) -⚬ (Done |+| Done)
def selectNeed : (Need |&| Need) -⚬ (Need |*| Need)
```

The main difference is that only the winning signal is consumed by the race.
The slower signal still has to be awaited at some point, so it is propagated to the other side of `-⚬`:

- In `raceDone`, if the first `Done` signal of the in-port wins, the second one is returned on the left of the `|+|`
  in the out-port. The case of second signal winning is analogous.
- In `selectNeed`, if the first `Need` signal of the _out_-port wins, the left side of the `|&|` in the in-port is
  chosen and the second `Need` signal of the out-port is forwarded to it.

There are additional library functions for racing built on top of these, provided for convenience.

### Racing is a source of non-determinism

The order of two concurrently occurring events is undefined. The outcome of a racing operation on two concurrent events
will therefore be non-deterministic. The non-determinism is propagated by proceeding differently for different winners
of the race.

## Using Scala values and functions

Libretto provides means to use _immutable_ Scala values and _total_ Scala functions in Libretto programs.

The type `Val[A]` represents a Scala value of type `A` flowing in the positive direction (i.e. along the `-⚬`).
Similarly, the type `Neg[A]` represents a Scala value of type `A` flowing in the negative direction
(i.e. against the `-⚬`).

For a first approximation, `Val[A]` can be thought of as `Future[A]` and `Neg[A]` can be thought of as `Promise[A]`.

To initially get some Scala values into a Libretto program, we bake them in during assembly using the primitives

```scala
def constVal[A](a: A): Done -⚬ Val[A]
def constNeg[A](a: A): Neg[A] -⚬ Need
```

Notice the incoming signals, `Done` and `Need`, respectively. Given that signals cannot be ignored, the responsibility
to handle a signal is transformed into a responsibility to handle a Scala value. This is OK, because Scala values cannot
be completely ignored, either. Doing so would mean to lose track of an ongoing potentially expensive computation and
thus a resource leak.

However, the particular value inside `Val` or `Neg` can be ignored; we just have to keep the liability to await the
computation. For this purpose, there are primitives to convert Scala values into signals:

```scala
def neglect[A]: Val[A] -⚬ Done
def inflate[A]: Need -⚬ Neg[A]
```

On the other hand, values can be duplicated, using

```scala
def dup   [A]: Val[A] -⚬ (Val[A] |*| Val[A])
def dupNeg[A]: (Neg[A] |*| Neg[A]) -⚬ Neg[A]
```

Because of this ability to duplicate values, it is preferable to use only _immutable_ values.

To apply a Scala function to a Scala value inside a Libretto program, we can use one of the primitives

```scala
def       mapVal[A, B](f: A => B): Val[A] -⚬ Val[B]
def contramapNeg[A, B](f: A => B): Neg[B] -⚬ Neg[A]
```

Note that the Scala functions used must be _total,_ that is they must always terminate and never throw an exception.

It is preferable that the used functions also be _pure,_ but benign side-effects are OK. Just note that it is undefined
on which thread the function will execute, and that it may as well not execute at all.

We can convert between Scala pairs and Libretto concurrent pairs using

```scala
def   liftPair[A, B]: Val[(A, B)] -⚬ (Val[A] |*| Val[B])
def unliftPair[A, B]: (Val[A] |*| Val[B]) -⚬ Val[(A, B)]

def   liftNegPair[A, B]: Neg[(A, B)] -⚬ (Neg[A] |*| Neg[B])
def unliftNegPair[A, B]: (Neg[A] |*| Neg[B]) -⚬ Neg[(A, B)]
```

We can lift a decision made by Scala code into Libretto via

```scala
def liftEither[A, B]: Val[Either[A, B]] -⚬ (Val[A] |+| Val[B])
```

Just like signals, the direction of Scala values can be inverted:

```scala
//  ┏━━━━━━━━━━━━━━━┓                   ┏━━━━━━━━━━━━━━━┓
//  ┃  promise[A]   ┃                   ┃  fulfill[A]   ┃
//  ┃               ┞──────┐            ┞──────┐        ┃
//  ┃            ┌┄┄╎Neg[A]│←┄        ┄→╎Val[A]│┄┄┐     ┃
//  ┃            ┆  ┟──────┘            ┟──────┘  ┆     ┃
//  ┃            ┆  ┃                   ┃         ┆     ┃
//  ┃            ┆  ┞──────┐            ┞──────┐  ┆     ┃
//  ┃            └┄→╎Val[A]│┄→        ←┄╎Neg[A]│←┄┘     ┃
//  ┃               ┟──────┘            ┟──────┘        ┃
//  ┗━━━━━━━━━━━━━━━┛                   ┗━━━━━━━━━━━━━━━┛

def promise[A]: One -⚬ (Neg[A] |*| Val[A])
def fulfill[A]: (Val[A] |*| Neg[A]) -⚬ One
```

## Inverse Types

We have seen that some types of interaction come in pairs, where one is the inverse of the other,
meaning that the information flow in one is exactly opposite the information flow in the other.

Examples that we have encountered so far:

|  type  | inverse type |
| ------ | ------------ |
| `Done` | `Need` |
| `Ping` | `Pong` |
| `Val[A]` | `Neg[A]` |
| `One` | `One` |

We can obtain bigger types that are inverses of each other by forming concurrent pairs:

|  type  | inverse type |
| ------ | ------------ |
| `Done \|*\| Ping` | `Need \|*\| Pong` |
| `Val[A] \|*\| (Neg[B] \|*\| Need)` | `Neg[A] \|*\| (Val[B] \|*\| Done)` |
| ... | ... |

### Duality of ⊕ and &

⊕ and & are also inverses of each other:
 - in `A |+| B`, the decision of which branch will proceed is passed from left to right;
 - in `A |&| B`, the decision is passed from right to left.

|  type  | inverse type |
| ------ | ------------ |
| `Done \|+\| Val[A]` | `Need \|&\| Neg[A]` |
| ... | ... |

### Universal Inversions

There is a special type constructor, `-[_]`, whose meaning is that `-[A]` is the inverse of `A`.
We also say that `-[A]` is a _demand_ for `A`.

It works universally for all types `A`.
This is convenient, as to talk about the inverse of some complex type `A`
we don't have to manually spell out what its inverse would be.
We can just use `-[A]` to refer to the inverse of `A`.

The downside is that types now have two inverses.
For example, both `Need` and `-[Done]` are inverses of `Done`.
However, these are isomorphic and one can go back and forth between these
without changing the semantics of the program.

There are some primitive operations for working with inverses.

```
  ┏━━━━━━━━━━━┓               ┏━━━━━━━━━━━━━┓
  ┃ demand[A] ┃               ┃  supply[A]  ┃
  ┃           ┞────┐          ┞────┐        ┃
  ┃        ┌┄┄╎-[A]│          ╎  A │┄┄┐     ┃
  ┃        ┆  ┟────┘          ┟────┘  ┆     ┃
  ┃        ┆  ┃               ┃       ┆     ┃
  ┃        ┆  ┞────┐          ┞────┐  ┆     ┃
  ┃        └┄→╎  A │          ╎-[A]│←┄┘     ┃
  ┃           ┟────┘          ┟────┘        ┃
  ┗━━━━━━━━━━━┛               ┗━━━━━━━━━━━━━┛
```

```scala
def demand[A]: One -⚬ (-[A] |*| A)
def supply[A]: (A |*| -[A]) -⚬ One
```

Notice the similarity with the inverting operations that we have seen before:

```
  demand[A]            promise[A]             lInvertSignal        lInvertPongPing
┏━━━━━━━━━━━┓        ┏━━━━━━━━━━━┓            ┏━━━━━━━━━━┓         ┏━━━━━━━━━━┓
┃           ┞────┐   ┃           ┞──────┐     ┃          ┞────┐    ┃          ┞────┐
┃        ┌┄┄╎-[A]│   ┃        ┌┄┄╎Neg[A]│←┄   ┃       ┌┄┄╎Need│←┄  ┃       ┌┄┄╎Pong│←┄
┃        ┆  ┟────┘   ┃        ┆  ┟──────┘     ┃       ┆  ┟────┘    ┃       ┆  ┟────┘
┃        ┆  ┃        ┃        ┆  ┃            ┃       ┆  ┃         ┃       ┆  ┃
┃        ┆  ┞────┐   ┃        ┆  ┞──────┐     ┃       ┆  ┞────┐    ┃       ┆  ┞────┐
┃        └┄→╎  A │   ┃        └┄→╎Val[A]│┄→   ┃       └┄→╎Done│┄→  ┃       └┄→╎Ping│┄→
┃           ┟────┘   ┃           ┟──────┘     ┃          ┟────┘    ┃          ┟────┘
┗━━━━━━━━━━━┛        ┗━━━━━━━━━━━┛            ┗━━━━━━━━━━┛         ┗━━━━━━━━━━┛


   supply[A]            fulfill[A]            rInvertSignal       rInvertPingPong
┏━━━━━━━━━━━━━┓      ┏━━━━━━━━━━━━━━┓         ┏━━━━━━━━━━┓         ┏━━━━━━━━━━┓
┞────┐        ┃      ┞──────┐       ┃         ┞────┐     ┃         ┞────┐     ┃
╎  A │┄┄┐     ┃    ┄→╎Val[A]│┄┄┐    ┃       ┄→╎Done│┄┄┐  ┃       ┄→╎Ping│┄┄┐  ┃
┟────┘  ┆     ┃      ┟──────┘  ┆    ┃         ┟────┘  ┆  ┃         ┟────┘  ┆  ┃
┃       ┆     ┃      ┃         ┆    ┃         ┃       ┆  ┃         ┃       ┆  ┃
┞────┐  ┆     ┃      ┞──────┐  ┆    ┃         ┞────┐  ┆  ┃         ┞────┐  ┆  ┃
╎-[A]│←┄┘     ┃    ←┄╎Neg[A]│←┄┘    ┃       ←┄╎Need│←┄┘  ┃       ←┄╎Pong│←┄┘  ┃
┟────┘        ┃      ┟──────┘       ┃         ┟────┘     ┃         ┟────┘     ┃
┗━━━━━━━━━━━━━┛      ┗━━━━━━━━━━━━━━┛         ┗━━━━━━━━━━┛         ┗━━━━━━━━━━┛
```

Then there are primitives for splitting and joining inversions:

```
  demandSeparately        demandTogether
  ┏━━━━━━━━━━━┓           ┏━━━━━━━━━━━┓
  ┃           ┞────┐      ┞────┐      ┃
  ┞────┐      ╎-[A]│      ╎-[A]│      ┞────┐
  ╎ ⎡A⎤│      ┟────┘      ┟────┘      ╎ ⎡A⎤│
  ╎-⎢⊗⎥│      ┃           ┃           ╎-⎢⊗⎥│
  ╎ ⎣B⎦│      ┞────┐      ┞────┐      ╎ ⎣B⎦│
  ┟────┘      ╎-[B]│      ╎-[B]│      ┟────┘
  ┃           ┟────┘      ┟────┘      ┃
  ┗━━━━━━━━━━━┛           ┗━━━━━━━━━━━┛
```

```scala
def demandSeparately[A, B] : -[A |*| B] -⚬ (-[A] |*| -[B])
def demandTogether[A, B]   : (-[A] |*| -[B]) -⚬ -[A |*| B]
```

We can then derive other operations, like

```scala mdoc:nest
/**
  * ┏━━━━━━━━━━━┯━━━━━━━━━┯━━━━━━━━━━━┯━━━━━━━━━━━━━━━━━━━┓
  * ┞───┐       ├───┐     ├────┐      ├────┐              ┃
  * ╎--A│       ╎--A│     ╎--A │      ╎ -A │              ┃
  * ┟───┘       ├───┘     ╎  ⊗ │ swap ╎  ⊗ │ supply[-[A]] ┃
  * ┠╌╌╌╌╌╌╌╌╌╌╌┤ assocRL ╎ -A │      ╎--A │              ┃
  * ┃           ├───┐     ├────┘      ├────┘              ┃
  * ┃           ╎-A │     ├╌╌╌╌╌╌╌╌╌╌╌┴╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┨
  * ┃ demand[A] ╎ ⊗ │     ├───┐                           ┞───┐
  * ┃           ╎ A │     ╎ A │                           ╎ A │
  * ┃           ├───┘     ├───┘                           ┟───┘
  * ┗━━━━━━━━━━━┷━━━━━━━━━┷━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
  */
def doubleDemandElimination[A]: -[-[A]] -⚬ A =
  introSnd(demand[A]) > assocRL > elimFst(swap > supply[-[A]])
```

or the isomorphisms between `Need` and `-[Done]`, etc.

## Function Objects and Higher-Order Functions

In modern programming languages we are used to functions being first-class objects
that can be passed to or returned from other functions, so-called _higher-order functions._

In Libretto, there, too, are function objects and higher-order functions.
Unlike most functional programming languages, though, there is a syntactic distinction
between

 - _function as code,_ `-⚬`, which is a blueprint of a program, a value of the host language, and
 - _function object,_ `=⚬`, which is a resource in a _running_ program.

It makes sense to distinguish between the two, as they exist at different stages.

Note that `A =⚬ B` is _not_ a value that can be freely used any number of times.
It may have captured resources (i.e. it is a closure), and therefore must itself
be treated as a resource that has to be consumed exactly once.

Note that function _objects_ are not objects in the OOP sense. We call them
objects because

 - they exist at the _object-level_ (as opposed to the meta-level,
   where functions as code, `A -⚬ B`, exist);
 - they are the _internal hom objects_ in a monoidal category.

Function objects are introduced by `curry` and eliminated by `eval`:

```scala
def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C)
def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B
```

Or we could have chosen `uncurry` instead of `eval`, but they are reducible to each other:

```scala mdoc:nest
def uncurry[A, B, C](f: A -⚬ (B =⚬ C)): (A |*| B) -⚬ C =
  par(f, id[B]) > eval[B, C]

def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B =
  uncurry(id[A =⚬ B])
```

### Function Objects via Inversions

Interestingly, function objects in Libretto are expressible via inversions, namely

```scala
type =⚬[A, B] = -[A] |*| B
```

That's right, a function object `A =⚬ B` is just an interface of interaction which
demands `A` and (eventually) supplies `B`.

In particular, it is not a callback given to someone else to execute.
Instead, each side of the interface does its respective part, namely
the producer of `A =⚬ B` receives `A` and produces `B`, whereas
the consumer of `A =⚬ B` produces `A` and receives `B`:

```
    A =⚬ B
  ━━━━┯━━━━━━━━
      ├───┐
    ←┄╎-A │←┄
      ├───┘
      ├───┐
    ┄→╎ B │┄→
      ├───┘
  ━━━━┷━━━━━━━━
```

Note that there is no requirement that `B` is produced only after `A` is supplied.
The plain Scala analogue would be a pair `(Promise[A], Future[B])`. There
is no requirement that the future completes only after the promise has been fulfilled.

`curry` and `eval` are expressible in terms of `demand` and `supply`:

```scala mdoc:nest
def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C) =
  introFst(demand[B]) > assocLR > par(id[-[B]], swap > f)

def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B =
  swap > assocRL > elimFst(supply[A])
```

### λ.closure

Function objects can also be created via the `λ.closure` method.

```scala
def closure[A, B](f: $[A] => $[B]): $[A =⚬ B]
```

For comparison, here is the `λ` signature again:

```scala
def λ[A, B](f: $[A] => $[B]): A -⚬ B
```

While `λ` creates a Libretto function, `λ.closure` creates just an auxiliary expression `$[A =⚬ B]`
that can be used from the outer `λ` expression.

For example, we could reimplement `curry` like this:

```scala mdoc
def myCurry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C) =
  λ { a =>
    λ.closure { b =>
      f(a |*| b)
    }
  }
```

Notice how the argument of `λ.closure` captures the variable `a` from the outer scope, i.e. it is a closure.

Note that capturing outer variables is not allowed for `λ`-expressions.

## Equality of Libretto programs

There are equations (laws) that hold about Libretto arrows, such as

```scala
// given
val f: A -⚬ B
val g: B -⚬ C
val h: C -⚬ D

// then

(f > g) > h = f > (g > h)

id[A] > f = f = f > id[B]
```

```scala
par(id[A], id[B]) = id[A |*| B]
```

```scala
// given
val f: A -⚬ C
val g: B -⚬ C

// then
injectL[A, B] > either(f, g) = f
```

```scala
// given
val f: A => B

// then
mapVal[A, B](f) > neglect[B] = neglect[A]
```

and many more.

_But what does it mean for two Libretto programs to be equal?_

Obviously, the sides of the equations above have different source code, so they are not equal at the source code level.

_We say that two Libretto programs are equal if their causal dependency graphs are equivalent<sup>(*)</sup>._

<sup>(*)</sup> For now let's settle for some intuitive understanding of _causal dependency graphs_ and a suitable
equivalence on them. Precise definition is left for further work.

Note that in the presence of non-determinism arising from concurrency, a single program can have multiple possible
execution traces. (Again, precise definition of an execution trace is left for further work.)

A particular implementation of Libretto then determines a probability distribution of the possible execution traces
of a program.

Note that it is not required of a Libretto implementation that two equal Libretto programs have the same probability
distribution of execution traces, only that they have the same set of possible execution traces. In practice this means
that although two programs are equal, they might exhibit statistically different behaviors.

Finally, let's give an example of two programs that look the same on the outside, but are not equal:

```scala
//  ┏━━━━━━━━━━━━━┯━━━━━━━━━━━━━━┓              ┏━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
//  ┞────┐        ╎              ┞────┐         ┞────┐      id[Done]        ┞────┐
//  ╎Done│→┄┄┄┄┐  ╎       ┌┄┄┄┄┄→╎Done│         ╎Done│→┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄→╎Done│
//  ┟────┘     ┆  ├────┐  ┆      ┟────┘         ┟────┘                      ┟────┘
//  ┃    join  ├┄→╎Done│→┄┤ fork ┃         ≠    ┠╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┨
//  ┞────┐     ┆  ├────┘  ┆      ┞────┐         ┞────┐      id[Done]        ┞────┐
//  ╎Done│→┄┄┄┄┘  ╎       └┄┄┄┄┄→╎Done│         ╎Done│→┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄→╎Done│
//  ┟────┘        ╎              ┟────┘         ┟────┘                      ┟────┘
//  ┗━━━━━━━━━━━━━┷━━━━━━━━━━━━━━┛              ┗━━━━━━━━━━━━━━━━━━━━━━━━━━━┛

join > fork ≠ par(id[Done], id[Done])
```

In the program on the left, each of the output signals depends on both input signals, whereas in the program on the
right, each output signal depends only on the respective input signal. Clearly, their causal dependency graphs are
different, and thus the programs are not equal.
