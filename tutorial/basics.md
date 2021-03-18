# Libretto Basics

A concurrent program in Libretto DSL is a _pure value_ of a certain type (such as the type `One -⚬ Done` or
`One -⚬ Val[String]`).
Such a value is a mere _description,_ or _blueprint,_ of a program to be executed.
The blueprint can then be passed to an interpreter for execution.

Programmer's task is then to write Scala code that first assembles a blueprint and then
passes is to an interpreter for execution. We thus think of run-time as split into
**assembly time** and **execution time**.

## Setup

### sbt project setup

You will need Scala 3 in order to use Libretto. Add the Scala 3 plugin to your `project/plugins.sbt` file:

```sbt
addSbtPlugin("ch.epfl.lamp" % "sbt-dotty" % "0.5.3")
```

The plugin requires a fairly recent version of sbt. Specify the sbt version in your `project/build.properties` file:

```properties
sbt.version=1.4.7
```

In your `build.sbt`, set the Scala version to Scala 3 and add the dependency on Libretto:

```sbt
scalaVersion := "3.0.0-RC1"

libraryDependencies += "com.github.tomasmikula" %% "libretto" % "0.1.0"
```

Check [search.maven.org](https://search.maven.org/search?q=com.github.tomasmikula%20libretto) for the latest version of
Libretto.

### Your first Libretto application

To follow this tutorial with code, you can play within the context of a `StarterAppScala`:

```scala
import libretto.StarterAppScala

object HelloWorld extends StarterAppScala[String] {

  // place your code experiments here

  override def blueprint: One -⚬ Val[String] =
    done > constVal("Hello world!")
}
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

## The identity component

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

```scala
val f1: A -⚬ ((B |*| C) |*| D)
```

we can always get

```scala
val f2: A -⚬ (B |*| (C |*| D)) =
  f1 > assocLR
```

## Symmetry of ⊗

The relative order of ports does not matter, either.

If, for example, we have a component

```scala
/*  ┏━━━━━━━━━━━━━━━━┓
 *  ┞─┐              ┞─┐
 *  ╎A│              ╎C│
 *  ┟─┘              ┟─┘
 *  ┃       f1       ┞─┐
 *  ┃                ╎D│
 *  ┞─┐              ╎⊗│
 *  ╎B│              ╎E│
 *  ┟─┘              ┟─┘
 *  ┗━━━━━━━━━━━━━━━━┛
 *
 */
val f1: (A |*| B) -⚬ (C |*| (D |*| E))
```

and need

```scala
val f2: (B |*| A) -⚬ ((E |*| D) |*| C) = ???
```

we can easily get it using `swap`

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

```scala
/*  ┏━━━━━━━━━━━━┯━━━━━━━━━━━━━━━━┯━━━━━━━━━━━━━━━━┯━━━━━━━━━━━━━━━┓
 *  ┞─┐          ├─┐              ├─┐              ├─┐             ┞─┐
 *  ╎B│          ╎A│              ╎C│              ╎D│             ╎E│
 *  ┟─┘          ├─┘              ├─┘              ╎⊗│  swap[D, E] ╎⊗│
 *  ┃            ╎                ╎ swap[C, D ⊗ E] ╎E│             ╎D│
 *  ┃ swap[B, A] ╎       f1       ├─┐              ├─┘             ┟─┘
 *  ┃            ╎                ╎D│              ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┨
 *  ┞─┐          ├─┐              ╎⊗│              ├─┐             ┞─┐
 *  ╎A│          ╎B│              ╎E│              ╎C│    id[C]    ╎C│
 *  ┟─┘          ├─┘              ├─┘              ├─┘             ┟─┘
 *  ┗━━━━━━━━━━━━┷━━━━━━━━━━━━━━━━┷━━━━━━━━━━━━━━━━┷━━━━━━━━━━━━━━━┛
 */
val f2: (B |*| A) -⚬ ((E |*| D) |*| C) =
  swap[B, A] > f1 > swap[C, D |*| E] > par(swap[D, E], id[C])
```

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

## Signals, `Done` and `Need`

By a signal we mean a notification that some event has occurred. The signal itself carries no information about the
event, though, it only signals that the event has occurred.

There are two types for signals, differing in the direction in which they travel:
 - `Done`, which travels in the direction of `-⚬`, i.e. from left to right.
   We also call the direction of `-⚬` the _positive direction._
 - `Need`, which travels in the direction opposite to `-⚬`, i.e. from right to left.
   We also call the direction opposite to `-⚬` the _negative direction._

Signals are useful for creating causal dependencies: one component might wait for a signal from another component
before proceeding with further processing. For example, the signal might signal completion of a request and further
processing might be accepting another request, effectively sequencing request processing.

For someone used to `Future` and `Promise`, it might be helpful, _despite important differences,_ to initially view
 - `Done` as `Future[Unit]`,
 - `Need` as `Promise[Unit]`.

### Immediate signals

There are primitive components that fire a signal immediately. More precisely, as soon as the branch containing
the component becomes active, but we haven't seen any branching operators yet. These are

```scala
//  ┏━━━━━━━━━━━━┓               ┏━━━━━━━━━━━━━━┓
//  ┃            ┞────┐          ┞────┐         ┃
//  ┃    done    ╎Done│          ╎Need│  need   ┃
//  ┃            ┟────┘          ┟────┘         ┃
//  ┗━━━━━━━━━━━━┛               ┗━━━━━━━━━━━━━━┛

def done: One -⚬ Done
def need: Need -⚬ One
```

### Signals cannot be ignored

We have just seen that we can easily fire a signal without any prerequisites using `done` or `need`.
On the other hand, a signal cannot be ignored. Once created, a signal has to be propagated, typically serving as
a trigger for another action.

Ignoring a signal would be analogous to ignoring a fired `Future`, which means losing track of a running task and thus
a potential resource leak. In a way, an incoming signal, whether `Done` incoming from the left or `Need` incoming from
the right, is a liability.

### Forking and joining signals

_Forking_ a signal means that as soon as the signal arrives, two new signals are fired.

```scala
//  ┏━━━━━━━━━━━━━┓                 ┏━━━━━━━━━━━━━━━━┓
//  ┃             ┞────┐            ┞────┐           ┃
//  ┃             ╎Done│            ╎Need│           ┃
//  ┞────┐        ┟────┘            ┟────┘           ┞────┐
//  ╎Done│ fork   ┃                 ┃      forkNeed  ╎Need│
//  ┟────┘        ┞────┐            ┞────┐           ┟────┘
//  ┃             ╎Done│            ╎Need│           ┃
//  ┃             ┟────┘            ┟────┘           ┃
//  ┗━━━━━━━━━━━━━┛                 ┗━━━━━━━━━━━━━━━━┛

def fork     : Done -⚬ (Done |*| Done)
def forkNeed : (Need |*| Need) -⚬ Need
```

Remember that `Need` travels from right to left, so `forkNeed` has one `Need` signal on the right and two `Need` signals
on the left.

_Joining_ two signals means to fire a signal as soon as both signals arrive.

```scala
//  ┏━━━━━━━━━━━━━━━━┓                 ┏━━━━━━━━━━━━━━━━┓
//  ┞────┐           ┃                 ┃                ┞────┐
//  ╎Done│           ┃                 ┃                ╎Need│
//  ┟────┘           ┞────┐            ┞────┐           ┟────┘
//  ┃       join     ╎Done│            ╎Need│ joinNeed  ┃
//  ┞────┐           ┟────┘            ┟────┘           ┞────┐
//  ╎Done│           ┃                 ┃                ╎Need│
//  ┟────┘           ┃                 ┃                ┟────┘
//  ┗━━━━━━━━━━━━━━━━┛                 ┗━━━━━━━━━━━━━━━━┛

def join     : (Done |*| Done) -⚬ Done
def joinNeed : Need -⚬ (Need |*| Need)
```

### Inverting signals

There are primitives to invert the direction of a signal.
A `Need` signal traveling to the left can be changed to a `Done` signal traveling to the right.
A `Done` signal traveling to the right can be changed to a `Need` signal traveling to the left.

```scala
//  ┏━━━━━━━━━━━━━━━┓                 ┏━━━━━━━━━━━━━━━┓
//  ┃ lInvertSignal ┃                 ┃ rInvertSignal ┃
//  ┃               ┞────┐            ┞────┐          ┃
//  ┃            ┌┄┄╎Need│←┄        ┄→╎Done│┄┄┐       ┃
//  ┃            ┆  ┟────┘            ┟────┘  ┆       ┃
//  ┃            ┆  ┃                 ┃       ┆       ┃
//  ┃            ┆  ┞────┐            ┞────┐  ┆       ┃
//  ┃            └┄→╎Done│┄→        ←┄╎Need│←┄┘       ┃
//  ┃               ┟────┘            ┟────┘          ┃
//  ┗━━━━━━━━━━━━━━━┛                 ┗━━━━━━━━━━━━━━━┛


def lInvertSignal: One -⚬ (Need |*| Done)
def rInvertSignal: (Done |*| Need) -⚬ One
```

Using these, we can always move a signal to the other side of the `-⚬` arrow while changing its direction.
For example, given

```scala
/*  ┏━━━━━━━━━━━━┓
 *  ┞────┐       ┃
 *  ╎Done│       ┃
 *  ┟────┘   f   ┃
 *  ┞────┐       ┞────┐
 *  ╎ A  │       ╎ B  │
 *  ┟────┘       ┟────┘
 *  ┗━━━━━━━━━━━━┛
 */
val f: (Done |*| A) -⚬ B
```

we can always obtain

```scala
/*  ┏━━━━━━━━━━━━━┓
 *  ┃             ┞────┐
 *  ┃             ╎Need│
 *  ┃       g     ┟────┘
 *  ┞────┐        ┞────┐
 *  ╎ A  │        ╎ B  │
 *  ┟────┘        ┟────┘
 *  ┗━━━━━━━━━━━━━┛
 */
val g: A -⚬ (Need |*| B)
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

```scala
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
val g: A -⚬ (Need |*| B) =
  introFst[A] > par(lInvertSignal, id[A]) > assocLR > par(id[Need], f)
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

Once it is decided which branch it is going to be, the corresponding component, `f` or `g`, is executed:

```
  ┏━━━━━━━━━━━━━━┓                          ┏━━━━━━━━━━━━━━┓
  ┞───┬────────╮ ┃                          ┞───┐          ┃
  ╎*A*╎   f    ╰─╀───┐                      ╎ A │     ╭────╀───┐
  ╎ ⊕ ├─────╮    ╎ C │                      ╎ ⊕ ├─────╯    ╎ C │
  ╎ B │     ╰────╁───┘                      ╎*B*╎   g    ╭─╁───┘
  ┟───┘          ┃                          ┟───┴────────╯ ┃
  ┗━━━━━━━━━━━━━━┛                          ┗━━━━━━━━━━━━━━┛
```

## Choice (&)

Type `A & B` (we use `A |&| B` in code to avoid confusion with the bitwise and operator in Scala, and for consistency
with `|*|` and `|+|`) means an _exclusive_ choice between `A` and `B`.
The component to the right of `A & B`, i.e. the one that has `A & B` as an in-port, gets to choose whether
the interaction with the component to the left will continue as `A` or as `B`.
The component to the left of `A & B`, i.e. the one that has `A & B` as an out-port, has to be able to provide
either of them (but not both of them simultaneously).
That is, the decision flows from right to left (the negative direction).

Primitives for choosing one of the branches (eliminating `|&|`) are

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

```scala
def coFactorL[A, B, C]: (A |*| (B |&| C)) -⚬ ((A |*| B) |&| (A |*| C)) =
  choice(par(id, chooseL), par(id, chooseR))

def coFactorR[A, B, C]: ((A |&| B) |*| C) -⚬ ((A |*| C) |&| (B |*| C)) =
  choice(par(chooseL, id), par(chooseR, id))
```

## Linearity and point-free style

When composing components into larger components, it cannot happen that somewhere inside a composite component
some ports remain unconnected. The way composition works, all ports of a constituent component that the composition
operator does not connect to other ports become ports of the composite component.
It also cannot happen that some port is connected twice.
The property of each port being connected exactly once is called _linearity_—data and resources flow through the system
in a linear fashion, without being duplicated or ignored (except via explicit operators for precisely that purpose).

Notice that building Libretto components is like composing Scala functions in _point-free style._
For a moment, forget the differences between `-⚬` and `=>` and view in-ports as function inputs.
In Libretto, we define the (linear) function without ever having access to the inputs as Scala values.
Indeed, user code will never have access to values of types like `One`, `Done`, `Need`, `A |*| B`, `A |+| B`, `A & B`
or others that we will encounter later. If it did, it would break linearity,
because Scala functions can freely ignore or duplicate (references to) values.

Moreover, not only are values of the above types not accessible to a user, there need not be any values of these
types at all. In fact, they are all uninhabited types in the proof-of-concept implementation. This should not be
surprising when you realize that Libretto's linear functions are mere blueprints. What then flows in a running system
when the blueprint is executed need not be values of the auxiliary formal types used in blueprints.

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

```scala
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

```scala
object List {
  def nil[A]: One -⚬ List[A] =
    injectL > pack

  //     head --+       +-- tail
  //            |       |       
  //            V       V       
  def cons[A]: (A |*| List[A]) -⚬ List[A] =
    injectR > pack
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

```scala
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

Libretto provides functions for testing which of two concurrent signals arrived first. There is one version for
`Done` signals and one for `Need` signals (although it is possible to implement one in terms of the other via
signal inversions discussed above).

```scala
def raceDone   : (Done |*| Done) -⚬ (Done |+| Done)
def selectNeed : (Need |&| Need) -⚬ (Need |*| Need)
```

In `raceDone`, the two `Done` signals from the in-port race against each other.
In `selectNeed`, the two `Need` signals from the out-port race against each other.

In both cases, the winning signal is consumed by the racing operation. The slower signal still has to be awaited
at some point (remember that signals cannot be ignored), so it is propagated to the other side of `-⚬`:
 - In `raceDone`, if the first `Done` signal of the in-port wins, the second one is returned on the left of the `|+|`
   in the out-port. The case of second signal winning is analogous.
 - In `selectNeed`, if the first `Need` signal of the out-port wins, the left side of the `|&|` in the in-port is
   chosen and the second `Need` signal of the out-port is forwarded to it.
   
There are additional library functions for racing built on top of these provided for convenience.

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
