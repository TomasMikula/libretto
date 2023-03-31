## Processing Sunflowers

This example implements a stream operator that consumes sunflowers and produces sunflowers oil and roasted sunflower seeds

### Input

 - source of sunflowers

### Output

 - source of packs of roasted seeds
 - source of bottles of sunflower oil

### Details

 - The two output sources compete for the input source of sunflowers.
 - It takes
   - 3 sunflowers to produce a pack of roasted seeds
   - 5 sunflowers to produce a bottle of sunflower oil
 - The stream operator should start working on the item corresponding to the output that pulls first.
   - Use the 3 (or 5) _successive_ sunflowers for that item.
 - Stop when either
   - both downstreams close;
   - upstream runs out of sunflowers.

### The example demonstrates

 - A stream operator with _multiple output_ streams.
 - _Racing_ of downstreams for access to the input source.
 - Declarative implementation without side-effects, synchronization primitives, etc.
