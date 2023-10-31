## Analysis of `Data` objects

We ran the `redeemers`, `datums`, and `script-data` analyses (see
[README.md](./README.md) on all mainnet script events up to mid-October 2023
(event file beginning `0000000105908766`; 21,832,781 script events in total).
The data involved 21,832,783 redeemers, 20,925,099 datum objects, and 16,736,891
`Data` objects in scripts.

Recall that these analyses record the following quantities:

* `memUsage`:  the total memory usage of the object (in 8-byte words) as given by `memoryUsage`.  This is not the actual
    amount of memory used, but an approximation.
* `numNodes`: the total number of nodes in the object.
* `depth`: the depth of the `Data` object.
* `numI`: the number of `I` nodes (these contain Integer values).
* `maxIsize`: the maximum `memoryUsage` over all `I` nodes.
* `totalIsize`: the total `memoryUsage` of all `I` nodes.
* `numB`: the number of `I` nodes (these contain ByteString values).
* `maxBsize`: the maximum `memoryUsage` over all `B` nodes.
* `totalBsize`: the total `memoryUsage` of all `B` nodes.
* `numL`: the number of `List` nodes.
* `maxL`: the largest length of a `List` node in the object.
* `numC`: the number of `Constr` nodes.
* `maxC`: the largest number of arguments in a `Constr` node in the object.
* `numM`: the number of `Map` nodes.
* `maxM`: the largest length of a `Map` node in the object.


### Redeemers