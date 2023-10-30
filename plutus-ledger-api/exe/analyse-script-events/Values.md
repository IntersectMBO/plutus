## `Value` objects involved in mainnet script events

We ran the `values` analysis (see [README.md](./README.md) on all mainnet script
events up to mid-October 2024 (event file beginning `0000000105908766`;
21,832,781 script events in total).


### `Value`s appearing in trasaction outputs

A total of 101,206,334 `Value` objects appeared in transaction outputs (for both
spending and minting scripts).  The frequencies of the most common twenty shapes
of `Value`s were as follows:

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

