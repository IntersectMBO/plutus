## Analysis of mainnet script events

The `analyse-script-events` executable provides some simple analyses of on-chain
script events.  In order to use this you must have a dump of the script events
that have occurred on the Cardano blockchain: instructions on how to do this can
be found in
[test-onchain-evaluation/README.md](../test-onchain-evaluation/README.md).  The
dump consists of a number of `.bz2` files with names like

```
0000000105908766-ae0fda07afb26a9c0636e7578cc10e379393ed830e7f7574d60032004da6287a.event.bz2
```

The first part of the name specifies the slot containing the first script event
in the file; the number of events per file is not fixed, but the more recent
files typically contain about 50,000 events.  The files contain scripts which
have been run on the chain, together with their inputs encoded using the
[Data](https://github.com/IntersectMBO/plutus/blob/master/plutus-core/plutus-core/src/PlutusCore/Data.hs)
type. For standard validation scripts the inputs consist of datum, redeemer, and
script context; for minting policies the inputs are a redeemer and script
context.

To run an analysis type
```
cabal run analyse-script-events <dir> <analysis>.
```

The `dir` argument specifies the path to a directory containing uncompressed
`.event` files (possibly the full set, or perhaps just a subset).  It may take
several hours for the analysis to complete depending on the complexity of the
analysis and the number of files to be analysed.

There are currently five analyses available:
* `datums`: analyse the structure of `Data` objects containing transaction datums
* `redeemers`: analyse the structure of `Data` objects containing redeemers
* `script-data`: analyse the structure of `Data` objects occurring inside scripts
* `values`: analyse the shape of `Value` objects occurring in script contexts
* `count-builtins` : count the total number of occurrences of each builtin in validator scripts

### `Data` object analyses

The `datums`, `redeemers`, and `script-data` analyses all collect statistics about `Data` objects.

These all print out a table of the form

```
memUsage numNodes depth numI maxIsize totalIsize numB maxBsize totalBsize numL maxL numC maxC numM maxM
     5       1      1     1     1          1       0    0           0       0    0    0    0    0    0
     4       1      1     0     0          0       0    0           0       1    0    0    0    0    0
   939     187      6    40     1         40     120    7         151       1    2    0    0   26   19
     5       1      1     1     1          1       0    0           0       0    0    0    0    0    0
...
```

The table can subjected to further analysis as required: for example it can be
directly loaded into R as a frame.

The fields are as follows:

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

A discussion of the `Data` objects involved in transactions up to mid-October
2023 can be found in [Data.md](./Data.md).


### `Value` analysis

The `values` analysis prints out information about `Value` objects (ie, amounts
of currencies) involved in transactions.  Its output looks like this, with one
entry for every transaction.

```
----------------
V1 Spending
Fee:     [1: 1]
Mint:    [1: 1]
Outputs:  2 [1: 1], [2: 1,1] [5: 1,7,2,0,3]
----------------
V1 Minting
Fee:     [1: 1]
Mint:    [2: 1,2]
Outputs:  2 [1: 1], [3: 1,1,2]
...
```

A `Value` consists of a map from currency identifiers to quantities of the
relevant currency, each quantity consisting of a map from token names to a
(positive or negative) integral number saying how many of the relevant tokens
the `Value` contains.  The output describes the "shape" of `Values` using lists
of the form `[5: 1,7,2,0,3]`, as seen above: this describes a value involving
five currency symbols, with the first involving one token, the second involving
seven, and so on.  The actual quantities of the individual tokens are not
printed.  The first entry in a `Value` is typically an amount of Ada, which has
a single currency symbol with only one token: all `Fee` values are of this form,
for example.

The output can be analysed as required.  For example, the shell script below
will produce a list of all the shapes of values ordered by frequency.  A
discussion of the `Value` objects appearing in script outputs up to mid-October
2023 can be found in [Values.md](./Values.md).

```

#!/bin/bash
grep "^Outputs" $1 |
sed 's/^Outputs: *[0-9]* *//' |
sed 's/, /\n/g' > osort.tmp

echo "Total: $(wc -l osort.tmp | awk '{print $1}')"
echo

sed 's/\[/\[ /' osort.tmp |
sort -n -k2 | uniq -c |
sort -nrs | sed 's/\[ /\[/'

rm osort.tmp
```

### Builtin analysis

The `count-builtins` analysis simply traverses the AST of each validator script
and accumulates the total number of times each built-in function appears,
printing out a table of frequencies once every validatorhas been processed.  See
[Builtins.md](./Builtins.md) for an example.

