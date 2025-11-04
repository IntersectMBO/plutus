## `Value` objects involved in mainnet script events

We ran the `values` analysis (see [README.md](./README.md)) on all mainnet script
events up to mid-October 2023 (event file beginning `0000000105908766`;
21,832,781 script events in total).


Recall that a `Value` consists of a map from currency identifiers to quantities
of the relevant currency, each quantity consisting of a map from token names to
a (positive or negative) integral number saying how many of the relevant tokens
the `Value` contains.  As in [README.md](./README.md), we describe `Value` objects
by their "shape", symbols of the form `[5: 1,7,2,0,3]` where the first number
is the number of currency symbols involved in the map and the following vector
of numbers gives the number of `TokenName`s for each currency symbol.

### `Value`s appearing in transaction outputs

A total of 101,206,333 `Value` objects appeared in transaction outputs (for both
spending and minting scripts, ignoring a single transaction with no outputs).
The frequencies of the most common twenty shapes of `Value`s were as follows:

```
37136006 [1: 1]
32143383 [2: 1,1]
18069772 [3: 1,1,1]
7784439  [4: 1,1,1,1]
2961328  [5: 1,1,1,1,1]
 611087  [3: 1,2,1]
 293372  [2: 1,2]
 156542  [2: 1,3]
  59061  [6: 1,1,1,1,1,1]
  48999  [2: 1,4]
  41511  [2: 1,5]
  36573  [7: 1,1,1,1,1,1,1]
  35298  [2: 1,20]
  32660  [2: 1,10]
  27775  [8: 1,1,1,1,1,1,1,1]
  25319  [3: 1,1,2]
  23608  [4: 1,1,2,1]
  22990  [2: 1,6]
  19163  [2: 1,9]
  15766  [4: 1,1,1,2]
  15705  [9: 1,1,1,1,1,1,1,1,1]
  14832  [11: 1,1,1,1,1,1,1,1,1,1,1]
  13529  [12: 1,1,1,1,1,1,1,1,1,1,1,1]
  13424  [10: 1,1,1,1,1,1,1,1,1,1]
  13265  [4: 1,2,1,1]
  12987  [2: 1,8]
  12908  [2: 1,7]
   9677  [13: 1,1,1,1,1,1,1,1,1,1,1,1,1]
   9497  [3: 1,3,1]
   8797  [3: 1,1,3]
```

These account for 99.48% of all output shapes. As can be seen, there are
typically only a few different currency symbols and the mostly have a small
number of tokens.  We found that 902089 outputs (0.89% of the total) involved
more than 10 currency symbols, 391029 (0.39%) involved more than 10, and 71713
(0.07%) involved more than 50; the maximum number of currency symbols in an
output was 119.

#### Token counts in transaction outputs

We use the term "token count" to describe the total number of `TokenName`s in a
value: it can be obtained by adding up the comma-separated values in the vector
at the end of the shape.  The table below shows the frequencies of token counts
of values appearing in transaction outputs.  The second column gives the token
count and the first the number of times a `Value` with that token count appears.
Again there are a total of 101206333 `Value`s.  As with currency symbols, the
figures are dominated by `Value`s with small token counts:

```
  37136006   1
  32143383   2
  18363144   3
   8577387   4
   3085382   5
    150131   6
    105781   7
     83094   8
     67265   9
     70596  10
     82978  11
     53927  12
     46368  13
     43146  14
     39930  15
     38185  16
     37308  17
     37278  18
     41202  19
     51047  20
    238719  21
     26418  22
     21040  23
     18770  24
     17071  25
     16206  26
     15353  27
     15235  28
     14204  29
     13765  30
```

`Value`s with a token count of five or less appear 99,305,302 times (98.12% of
the total number of `Value`s).  The maximum token count is 548, and only 137643
`Value`s (0.13%) have a token count greater than 100.  It is difficult to
quantify precisely, but it seems that it is very rare to have a `Value` which
has a large number of currency symbols each with a large number of different
token names.  For example, for almost all `Value`s with more than 100 currency
symbols, typically at least 90% the currency symbols have only a single
associated token name, and there will be a maximum of two or three currency
symbols whose number of token names is in double figures.

There are some `Value`s where each currency symbol has a large number of tokens,
but these generally only have a small number of currency symbols (and appear in
only a small number of transactions): typical shapes are `[ 3 : 1,109,147 ]` and
`[ 5 : 1,10,3,17,36 ]`, and as the number of currency symbols increases the
number of token names decreases.

The overall conclusion is that (at least at the time of writing) the vast
majority of `Value` objects in transaction outputs are quite simple: they
generally have only a few currency symbols and each currency symbol has only a
few (often only one) associated token names.


## `Value`s minted in transactions

Transactions can also mint currencies.  For reference we include a table of the
frequencies of shapes of values minted in the mainnet transactions.  Note that
_every_ transaction contains a minting value for Ada, but this will always be
zero in the transactions examined here.  All of the transactions in the first
entry minted nothing: they have a single entry which mints zero Ada


```
18768238 [1: 1]
 2474390 [2: 1,1]
  223484 [2: 1,3]
  138712 [2: 1,2]
   99134 [2: 1,4]
   61153 [3: 1,1,1]
   40275 [2: 1,5]
   15552 [4: 1,1,1,1]
    6632 [2: 1,6]
    1990 [2: 1,7]
     700 [3: 1,1,2]
     657 [2: 1,20]
     363 [2: 1,10]
     348 [3: 1,20,20]
     272 [3: 1,2,1]
     145 [2: 1,12]
     112 [2: 1,8]
      78 [3: 1,2,3]
      66 [3: 1,3,1]
      59 [2: 1,14]
      53 [2: 1,15]
      44 [2: 1,11]
      37 [5: 1,1,1,1,1]
      36 [3: 1,3,2]
      35 [6: 1,1,1,1,1,1]
      32 [3: 1,2,2]
      30 [31: 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
      28 [29: 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
      19 [2: 1,17]
      18 [2: 1,16]
      12 [7: 1,1,1,1,1,1,1]
      12 [3: 1,4,1]
      12 [13: 1,1,1,1,1,1,1,1,1,1,1,1,1]
      10 [11: 1,1,1,1,1,1,1,1,1,1,1]
       8 [3: 1,6,1]
       7 [2: 1,9]
       6 [2: 1,13]
       5 [2: 1,19]
       4 [3: 1,14,14]
       4 [3: 1,1,3]
       3 [2: 1,25]
       2 [2: 1,100]
       1 [2: 1,60]
       1 [2: 1,29]
       1 [2: 1,27]
       1 [2: 1,18]
```
