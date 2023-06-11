## Packaging Dog Presents

This example implements a custom **stream operator** for packaging dog presents.

### Inputs
 - sources of dog toys
 - source of bones (a bone can be large or small)
 - source of dog biscuits

### Outputs
 - source of wrapped dog presents

### Details

Each present contains either:
 - 1 toy, 1 large bone, 3 dog biscuits
 - 1 toy, 1 small bone, 5 dog biscuits

The operator stops when
 - any of the upstreams runs out of items; or
 - there's no more downstream demand.

### This example demonstrates

 - a stream operator driven by downstream demand
   - with multiple input streams
   - whose pulling behavior (from biscuits) depends on a previously pulled value (from bones)
   - implemented declaratively, without effects.
