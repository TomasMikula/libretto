# Dining Philosphers

The dining philosphers problem is a model problem in concurrent programming.
Here is the problem statement taken from the [Wikipedia article](https://en.wikipedia.org/wiki/Dining_philosophers_problem):

> Five silent philosophers sit at a round table with bowls of spaghetti. Forks are placed between each pair of adjacent philosophers.
>
> Each philosopher must alternately think and eat. However, a philosopher can only eat spaghetti when they have both left and right forks. Each fork can be held by only one philosopher at a time and so a philosopher can use the fork only if it is not being used by another philosopher. After an individual philosopher finishes eating, they need to put down both forks so that the forks become available to others. A philosopher can only take the fork on their right or the one on their left as they become available and they cannot start eating before getting both forks.
>
> Eating is not limited by the remaining amounts of spaghetti or stomach space; an infinite supply and an infinite demand are assumed.
>
> The problem is how to design a discipline of behavior (a concurrent algorithm) such that no philosopher will starve; i.e., each can forever continue to alternate between eating and thinking, assuming that no philosopher can know when others may want to eat or think.

The solution presented here
 - uses a `Lock` (from Libretto's library) to represent a fork (a resource that is owned by at most one user at a time).
   Note, however, that `Lock` is not a primitive in Libretto. It is implemented using other primitives, most importantly racing;
 - relies on randomness to prevent any one philosopher from starving.

## Running the example

Run

```
sbt examples/run
```

and then choose the number of the `DiningPhilosophers` example.
