# Libretto Basics

A concurrent program in Libretto DSL is a _pure value_ of a certain type (such as the type `One -⚬ Done`).
Such a value is a mere _description,_ or _blueprint,_ of a program to be executed.
The blueprint can then be passed to an interpreter for execution.

Programmer's task is then to write Scala code that first assembles a blueprint and then
passes is to an interpreter for execution. We thus think of run-time as split into
**assembly time** and **execution time**.

## Building blocks

Libretto programs are composed of blocks with typed **in-ports** and **out-ports**,
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

The in-ports and out-ports define the _interface_ of a block.

We can think of a block as a part of a system that runs autonomously and communicates with the rest of the system
through its in-ports and out-ports.

☝️ Do _not_ assume that through in-ports information flows into the block and through out-ports information flows out
of the block. That may or may not be the case. In general, information may flow in either direction or even in both
directions through an in-port as well as through an out-port. However, the distinction between in-ports and out-ports
is important for composition, see below.

## Sequential composition

We can connect an out-port to an in-port (but not to another out-port) of the same type on another block. For example,
these two blocks `f` and `g`

```
┏━━━━━━━━━━━━┓    ┏━━━━━━━━━━━━┓   
┞─┐          ┞─┐  ┞─┐          ┞─┐ 
╎A│    f     ╎B│  ╎B│    g     ╎C│ 
┟─┘          ┟─┘  ┟─┘          ┟─┘ 
┗━━━━━━━━━━━━┛    ┗━━━━━━━━━━━━┛   
```

can be composed into a composite block `g ⚬ f`

```
┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓  
┞─┐                            ┞─┐
╎A│           g ⚬ f            ╎C│
┟─┘                            ┟─┘
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛  
```

☝️ Although we call it _sequential_ composition, do _not_ assume that`g` takes place "after" `f`, in a temporal or
ocausal sense. That may or may not be the case and we would need know the interface type `B` and possibly the inner
workings of the blocks to make judgments about causal dependence. In general, processing can take place in `g` even
before any information passes through the `B` interface.

## Parallel composition

Any two blocks `f`, `g`

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

A block `f` with one in-port of type `A` and one out-port of type `B`

```
┏━━━━━━━━━━━━┓
┞─┐          ┞─┐
╎A│    f     ╎B│
┟─┘          ┟─┘
┗━━━━━━━━━━━━┛
```

is a value `f` of type `A -⚬ B`.

The funny arrow-like symbol, `-⚬`, also called a _lollipop_, is borrowed from linear logic where it denotes _linear
implication_ and in Libretto we also call it a _linear function._

☝️ Although we call `-⚬` a linear _fuction,_ some intuitions one might have about Scala functions (`=>`) do not
transfer to `-⚬`. With a Scala function, there is nothing going on inside it until we pass all the inputs to it.
Once we get the output (and we get the whole output all at once), the Scala function is done. Remember, however,
that Libretto's linear function is a block, a part of the system that runs on its own and perhaps communicates
with its environment through the ports.

In Scala, we model multiple in-ports as a single in-port of a composite type, and similarly for out-ports.
As an example, a block `f` with two in-ports of types `A` and `B` and two out-ports of types `C` and `D`

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

is represented as a value `f: (A ⊗ B) -⚬ (C ⊗ D)`. As one would guess, _X ⊗ Y_ represents a _pair_ of _X_ and _Y_.
The operator _⊗_ is called a _tensor product,_ sometimes referred to as _times_.

Because the ⊗ symbol is usually not very intelligible in monospace fonts (e.g. hardly distinguishable from ⊕, compare
`⊗` vs. `⊕`), in code we usually use `|*|` for tensor product. The above block is then `f: (A |*| B) -⚬ (C |*| D)`.

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

## The identity function

For any type `A` there is an _identity_ function

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

If we are designing a block with more than two in-ports or out-ports, such as this one,

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
For the above block, there are two possibilities:

```scala
f1: A -⚬ ((B |*| C) |*| D)
f2: A -⚬ (B |*| (C |*| D))
```

Sometimes one way is more natural than the other, but often it is an arbitrary choice.
We need not worry about it too much, though, because the grouping does not matter:
we can always regroup the ports using

```scala
def timesAssocLR[X, Y, Z]: ((X |*| Y) |*| Z) -⚬ (X |*| (Y |*| Z))
def timesAssocRL[X, Y, Z]: (X |*| (Y |*| Z)) -⚬ ((X |*| Y) |*| Z)
```

```
┏━━━━━━━━━━━━━━━━┓             ┏━━━━━━━━━━━━━━━━┓  
┞─┐              ┞─┐           ┞─┐              ┞─┐
╎X│              ╎X│           ╎X│              ╎X│
╎⊗│              ┟─┘           ┟─┘              ╎⊗│
╎Y│ timesAssocLR ┞─┐           ┞─┐ timesAssocRL ╎Y│
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
  f1 > timesAssocLR
```

## Symmetry of ⊗

The relative order of ports does not matter, either.

If, for example, we have a block

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

Sometimes we want a block with no in-ports or no out-ports, such as these ones

```
┏━━━━━━━━━━━━┓            ┏━━━━━━━━━━━━┓  
┃            ┞─┐          ┞─┐          ┃
┃      f     ╎A│          ╎B│    g     ┃
┃            ┟─┘          ┟─┘          ┃
┗━━━━━━━━━━━━┛            ┗━━━━━━━━━━━━┛  
```

In Scala representation, however, we have to specify the type of in-port and the type of outport.
There is a special fake port type, `One`, through which there is no flow of information in either direction.

We can declare the above two blocks as

```scala
val f: One -⚬ A
val g: B -⚬ One
```

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
