# Performance of Scott Encoding vs. Explicit Datatypes in Haskell

head/tail of list:

| m | scott | builtin |
|___|_______|_________|
| 2 | 18.9ns | 5.5ns |
| 10 | 18.9ns | 5.51ns |
| 10^2 | 19.0ns | 5.77ns |
| 10^3 | 18.9ns | 5.51ns |
| 10^4 | 18.8ns | 5.51ns |
| 10^5 | 18.9ns | 5.51ns |

sum:

| m | scott | bulitin |
|---|-------|---------|
| 1 | 17.7ns | 7.63ns |
| 10 | 136ns | 35.2ns |
| 10^2 | 1.28us | 392ns |
| 10^3 | 13.1us | 3.88us |
| 10^4 | 196us | 93.9us |
| 10^5 | 2.9ms | 1.4ms |
| 10^6 | 32.6ms | 26.7ms |
| 10^7 | 355ms | 283ms |

quicksort

| m | scott | builtin |
|---|-------|---------|
| 1 | 53.9ns | 21.8ns |
| 10 | 290ns | 141ns |
| 10^2 | 2.68us | 1.58us |
| 10^3 | 33.2us | 19.8us |
| 10^4 | 386us | 236us |
| 10^5 | 5.92ms | 4.66ms |
| 10^6 | 31.2ms | 25.2ms |
| 10^7 | 357ms | 240ms |