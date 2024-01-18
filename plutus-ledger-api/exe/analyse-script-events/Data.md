## Analysis of `Data` objects

We ran the `redeemers`, `datums`, and `script-data` analyses (see
[README.md](./README.md)) on all mainnet script events up to mid-October 2023
(event file beginning `0000000105908766`; 21,832,781 script events in total).
The data involved 21,832,783 redeemers, 20,925,099 datum objects, and 16,736,891
`Data` objects in scripts. (There may be some small discrepancies in these
numbers compared with other experiments due to the treatment of some anomalous
scripts that were encountered during the course of experimentation, but these
are too small to affect the overall conclusions).

There are some tables of frequencies later in the document.  Note that some of
these show exact frequencies (eg, how many objects have a particular depth) but
that others (those mentioning `<=` in the rightmost column) show cumulative
frequencies (eg, what proportion of a dataset has size _no greater than_ the
number in the first column).

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


### `memoryUsage` of `Data` objects

The `memoryUsage` figure is of interest because the costs of some important
operations on `Data` depend on it. The maximum `memoryUsage` of a redeemer in
our dataset was 1588, the maximum for a datum was 1083, and the maximum for a
`Data` object in a script was 1099.  The table below shows the number of objects
in each dataset whose `memoryUsage` is less than or equal to the number in the
first column (and note that the numbers in the first column are not linearly
distributed).  There are some rounding errors here: for example, in the first
column there are only 4709 objects (of over 21 million) with `memoryUsage`
greater than 150, and 610 objects with `memoryUsage` greater than 400.  It is
clear that for redeemers and script data objects the `memoryUsage` is typically
less than about 50 and for datum objects it is typically less than about 200.


| mem <= |   Redeemer   |   Datum   | Script Data |
| :----: | :----------: | :-------: | :---------: |
|    5   |    31.32%    |  27.76%   |   31.32%    |
|   10   |    73.53%    |  29.99%   |   73.53%    |
|   15   |    78.16%    |  30.56%   |   78.16%    |
|   20   |    91.63%    |  33.70%   |   91.63%    |
|   25   |    96.58%    |  35.18%   |   96.58%    |
|   30   |    97.09%    |  36.38%   |   97.09%    |
|   35   |    97.12%    |  38.81%   |   97.12%    |
|   40   |    98.25%    |  42.33%   |   98.25%    |
|   45   |    98.25%    |  54.56%   |   98.25%    |
|   50   |    98.25%    |  58.01%   |   98.25%    |
|   55   |    98.26%    |  58.21%   |   98.26%    |
|   60   |    98.56%    |  58.48%   |   98.56%    |
|   65   |    98.62%    |  64.76%   |   98.62%    |
|   70   |    98.62%    |  66.98%   |   98.62%    |
|   75   |    98.62%    |  67.37%   |   98.62%    |
|   80   |    98.64%    |  67.59%   |   98.64%    |
|   85   |    98.64%    |  67.74%   |   98.64%    |
|   90   |    98.64%    |  71.89%   |   98.64%    |
|   95   |    98.68%    |  78.64%   |   98.68%    |
|  100   |    98.68%    |  79.51%   |   98.68%    |
|  125   |    99.18%    |  93.47%   |   99.18%    |
|  150   |    99.98%    |  93.53%   |   99.98%    |
|  175   |    99.98%    |  93.89%   |   99.98%    |
|  200   |    99.98%    |  93.90%   |   99.98%    |
|  300   |    99.98%    |  99.99%   |   99.98%    |
|  400   |    100.00%   |  100.00%  |   100.00%   |
|  500   |    100.00%   |  100.00%  |   100.00%   |


We spent some time thinking about the costs of `equalsData` and `serialiseData`
a while ago: see the comments for
[PR #4480](https://github.com/IntersectMBO/plutus/pull/4480).  The experiments
there used inputs of size up to 80,000, which is considerably larger than the
200 units we're likely to see in practice.  For an object of size 200, the CPU
cost of `equalsData` according to the current cost model is 1,073,158 ExCPU
(0.01% of the maximum 10,000,000,000 and about 77 Lovelace); for
`serialiseData` the cost is 79,693,724 ExCPU (0.79% of the maximum and about
5,746 Lovelace).  The memory cost of `equalsData` is 1 ExMem (effectively zero)
and the memory cost of `serialiseData` on an object of size 200 is 400 ExMem
(0.0028% of the maximum 14,000,000 and about 11 Lovelace).  This suggests that
despite the complexities of costing these operations the cost models we've ended
up with are entirely reasonable.



### Depths and number of nodes

The maximum depth of a redeemer object was 10, of a datum was 12, and of a
script `Data` object was 7.  The precise distribution of depths is shown below.
Again there are some rounding errors: for example, there is only one datum
object of depth greater than 10 and there only 803 of depth greater than 8.

 | depth  |   Redeemer   |  Datum    | Script Data |
 |:------:|:------------:|:---------:|:-----------:|
 |    1   |    76.21%    |  28.09%   |    73.04%   |
 |    2   |    12.01%    |  19.37%   |    13.63%   |
 |    3   |     2.00%    |   8.54%   |    12.16%   |
 |    4   |     2.42%    |   3.41%   |     0.04%   |
 |    5   |     0.01%    |   1.54%   |     1.12%   |
 |    6   |     7.33%    |  19.40%   |     0.02%   |
 |    7   |     0.01%    |   1.93%   |     0.01%   |
 |    8   |     0.00%    |  17.71%   |     0.00%   |
 |    9   |     0.00%    |   0.00%   |     0.00%   |
 |   10   |     0.00%    |   0.00%   |     0.00%   |
 |   11   |     0.00%    |   0.00%   |     0.00%   |
 |   12   |     0.00%    |   0.00%   |     0.00%   |



The maximum number of nodes was 300 for redeemers (mean 1.98), 357 for datums
(mean 11.86), and 139 for script objects (mean 1.93).  As the means suggest,
redeemers and script data objects are typically very small: only 12475 redeemers
have more than 9 nodes. and only 4175 data objects have more than 23 nodes.  The
distribution for datums is slightly more interesting, as shown below (these are
cumulative frequencies: the second column shows the number of datums with
at most `n` nodes, `n` being the number in the first column).

| nodes <= |   Datum  |
|:--------:|:--------:|
|     5    | 36.31%   |
|    10    | 58.27%   |
|    15    | 67.29%   |
|    20    | 79.72%   |
|    25    | 93.47%   |
|    30    | 93.53%   |
|    35    | 93.90%   |
|    40    | 93.95%   |
|    45    | 93.96%   |
|    50    | 99.99%   |
|    55    | 100.00%  |
|    60    | 100.00%  |

### Distribution of the different types of nodes

### `I` nodes

Nodes of type `I` contain `Integer` values, and these values are typically very
small. No redeemer or script `Data` object contains an integer of size greater
than 1, and only 6 datum objects do (5 contain integers of size 2 and a single
datum contains an integer of size 4).  Many objects have no `I` nodes at all:
this is the case for 79% of redeemers, 37% of datums, and 88% of script `Data`
objects.

### `B` nodes

Nodes of type `B` contain `ByteString` values. Again, redeemers and script
`Data` objects are not very interesting: 85% of redeemers contain no `B` nodes
at all and only 20810 (0.1%) contain more than two `B` nodes; the maximum number
of `B` nodes is 97, and the maximum `memoryUsage` (in 8-byte words) of a
bytestring in a `B` node is 18. The maximum total `memoryUsage` of bytestrings
(`totalBsize`) in a `B` node is 388.


In scripts, 28% of `Data` objects contain no `B` nodes, 52% contain one, and 19%
contain two; only 1.75% contain more than two `B` nodes; the maximum number of
`B` nodes is 137, and the maximum `memoryUsage` is 10. The maximum `totalBsize`
figure is 543.


The distribution of numbers of `B` nodes in datums is a little more interesting:


| `B` nodes |   Datum    |
| :-------: |:----------:|
|  0        |   30.97%   |
|  1        |    2.27%   |
|  2        |    5.44%   |
|  3        |    7.93%   |
|  4        |   17.80%   |
|  5        |    8.51%   |
|  6        |   18.79%   |
|  7        |    1.76%   |
|  8        |    0.00%   |
|  9        |    0.31%   |
| 10        |    0.00%   |
| 11        |    0.06%   |
| 12        |    0.01%   |
| 13        |    6.03%   |
| 14        |    0.00%   |
| 15        |    0.06%   |

The maximum number of `B` nodes in a datum is 242, and the maximum `memoryUsage`
of a bytestring in a `B` node is 57. The maximum `totalBsize` figure is 388.

### `List`, `Map`, and `Constr` nodes

For the complex node types (whose contents are essentially lists of one type or
another) we only recorded the total number of nodes (`numL`, `numM`, and `numC`)
and the maximum length of and list in these nodes (`maxL`, `maxM`, and `maxC`).
The maxima of these for each of our datasets are tabulated below.

|             | Redeemer |  Datum  | Script Data |
|:-----------:|:--------:|:-------:|:-----------:|
| max(numL)   |     8    |    6    |      3      |
| max(numM)   |     4    |   45    |      3      |
| max(numC)   |   195    |   34    |     23      |
|             |          |         |             |
| max(maxL)   |    59    |   59    |    135      |
| max(maxM)   |    21    |   30    |      1      |
| max(maxC)   |    14    |   16    |     40      |

In fact, the `List` and `Map` nodes are very seldom used.  Over 99.9% of all
`Data` objects in the entire dataset have two or fewer `List` nodes, and the
same is true for `Map` nodes in redeemers and script `Data` objects; there are
slightly more `Map` nodes in datums, but still over 99% have six or fewer `Map`
nodes.

`Constr` nodes are more common, although over 99% of redeemers and script `Data`
objects contain six or fewer such nodes.  There tend to be more `Constr` nodes in
datums, as shown by the table below

| numC |   Datum   |
|:----:|:---------:|
|  0   |   0.86%   |
|  1   |   46.25%  |
|  2   |    4.88%  |
|  3   |    0.86%  |
|  4   |    3.36%  |
|  5   |    4.61%  |
|  6   |    2.29%  |
|  7   |    4.08%  |
|  8   |    0.28%  |
|  9   |    0.06%  |
| 10   |    0.14%  |
| 11   |    7.54%  |
| 12   |    1.42%  |
| 13   |    5.38%  |
| 14   |   11.64%  |
| 15   |    0.31%  |
| 16   |    0.00%  |
| 17   |    0.00%  |
| 18   |    0.00%  |
| 19   |    0.00%  |
| 20   |    0.01%  |
| 21   |    0.00%  |
| 22   |    6.03%  |
| 23   |    0.00%  |

Only five datum objects (of almost 21 million) contain more than 22 `Constr`
nodes, but for some reason there are 1,260,972 datums with exactly 22.

## Conclusions

It seems that in general `Data` objects on the chain are quite small and simple,
especially redeemers and `Data` objects embedded in scripts.  Datum objects tend
to be larger and more complex, and it might be worth trying to understand why
this is.
