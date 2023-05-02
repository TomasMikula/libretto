## Digital Library of Alexandria

This example implements a stream operator to fetch digitized versions of papyrus scrolls from the library's server.

### Input

 - source of scroll IDs
 
### Output

 - source of scanned pages of all scrolls from the input, in the given order
 
### Details

 - We are provided with an API to fetch a stream of scanned pages for a given scroll ID. 
   - For the sake of solving this example, implementors are free to define type signature of the API that best suits them.
   - In our solution, we go as far as to wrap an imperative, blocking API from the `vendor` package. That is just to demonstrate ability to integrate with the (ugly) "real world", but is way beyond what is expected.
 - It might take a long time before we get any bytes in the response, while, on the server, a robot goes to fetch and scan the papyrus scroll.
 - The actual data transfer is then relatively fast.
 - The library's fair use policy allows at most _k_ concurrent connections.
 - Our task is to use all _k_ connections to prepare documents on the server concurrently, but transfer data sequentially, to preserve order.

### Why is the example interesting

The lifetimes of connections are overlapping, but do not form a nested hierarchy.

Therefore, the lifetimes do not map well to hierarchical resource scopes found in some other streaming libraries.

This fact makes it exceptionally hard to write a correct and resource-safe solutions with those libraries. (Please, let me know if you have one!)
