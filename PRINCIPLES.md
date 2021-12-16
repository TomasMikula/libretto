# Guiding Principles

## Locality

> [The] principle of locality states that an object is directly influenced only by its immediate surroundings.
>
> [...]
>
> The concept is that for an action at one point to have an influence at another point, something [...] between those points [...] must mediate the action.

— from Wikipedia: [Principle of locality](https://en.wikipedia.org/wiki/Principle_of_locality)

The concept is related to that of _continuity:_ any change is mediated by a _path_ without abrupt jumps.

We illustrate the concept of locality on many examples of _non_-locality in programming.

### Side-effects

Side-effects are spooky action at a distance, thus non-local.

### Callbacks

Callbacks are necessarily side-effectful, thus non-local.

### Shared/global mutable state

Mutations are side-effects, thus non-local. Instead, interact through a typed protocol.

### Dynamic typing

Runtime type errors are largely spooky action at a distance:
providing a value of the wrong type at one place causes a type error at a different place.

### (Unchecked) exceptions

Unchecked exceptions can pop out of nowhere and are therefore non-local.

### Illegal state representable

Leads to non-locality of reasoning: code can be proven correct only after considering larger context.

### Boolean blindness

The path connecting the meaning of the tested boolean to the respective branch of if-then-else is absent.

### Unhelpful error messages

The translation (i.e. path) of the error from the domain where it originated to the domain where it surfaced is missing (i.e. a discontinuity).

### Lost error messages

The path between the problem and the observer is missing.

### Long strikes without type annotations

The gap between the source code and its typechecked version is too big (i.e. a discontinuity). The reader has to re-do type inference in their head.

Also, a code change at one place can cause a type error at a distant place (i.e. non-locality).

### Many levels of implicit resolution

The gap between the source code and its explicit version is too big (i.e. a discontinuity). The reader has a hard time to reason about what value gets resolved.

Also, when a code change breaks the implicit resolution, a clear path from the change to the error is missing.

### Dependency injection

That is, when instances are constructed by "magic" (e.g. runtime reflection or compile-time macros).

The gap between the source code and its explicit version is too big (i.e. a discontinuity). The reader has a hard time to reason about what instance gets constructed.

Also, when a seemingly innocent code change causes construction of a wrong instance (i.e. a bug), it can easily go undetected.

### Clever tricks

There is a big gap (i.e. discontinuity) between the code and convincing oneself of its correctness.

### Assumptions about context

For example, an actor implementation making an assumption that the actor will be supervised by its parent.

The path from the place where the assumption is made to the place where it is satisfied (if at all) is missing.

### Concealed reading of configuration from the environment

The _environment_ is e.g. the file system, environment variables, Java system properties, ...

By _concealed_ we mean not communicated in the component's interface (reading config from an explicitly given file is by itself OK).

It is non-local, because the path from the config (file, env variable, ...) to its use is missing.

### Paradigm switch

Paradigm switch means an abrupt jump (i.e. a discontinuity) in the used mental and technological tools.

Paradigm switches often appear between:
 - client and server,
 - program and database,
 - application programming and DevOps.

We believe the need for paradigm switches at these boundaries is not fundamental, but rather accidental.