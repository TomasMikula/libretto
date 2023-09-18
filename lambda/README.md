# Libretto Lambda

Libretto Lambda lets DSL authors
 - give lambda (i.e. anonymous function) syntax to the DSL users;
 - _"delambdify"_ the lambda expressions and prodoce point-free representation of DSL programs;
 - thereby avoiding the inherent complexities of dealing with variable bindings.

The point-free representation is a composition of arrows of a certain category.
As a minimum, _symmetric semigroupal category_ is needed.
However, there is extra support for stronger categories, such as
_monoidal_ (adding and removing unit),
_cartesian_ (duplication aka. diagonal, projections),
_co-cartesian_ (co-products to represent branching),
_closed_ (function objects, higher-order functions).

## Examples

See [lambda-examples](../lambda-examples).
