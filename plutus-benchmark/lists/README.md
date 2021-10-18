This directory contains Plutus implementations of some simple list algorithms.
There are two sets of algorithms: `sort` and `sum`.

### `sort`

The `sort` directory contains Plutus implementations of insertion sort, merge
sort, and quicksort for Scott-encoded list.  The `list-sort-exe` executable runs
these with worst-case inputs of increasing length and prints out some statistics
(cost and number of CEK steps) and the `list-sort` benchmark contains Criterion
benchmarks to get actual times.  This gives us and idea of how large a list we
can sort in Plutus Core in a reasonable time.

### `sum`

The `sum` directory contains benchmarks which sum up lists of integers using
compiled and hand-written folds along Scott lists and built-in lists (ie,
 Haskell lists acessed as a built-in type in Plutus Core), allowing us to
see which type of list we can process most efficiently.



