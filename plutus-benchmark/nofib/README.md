## Plutus `nofib` benchmarks

This directory contains Plutus versions of some benchmarks from the
`spectral` set of [GHC nofib benchmarks](https://github.com/ghc/nofib).

Most of the programs have required some modifications in order to work as Plutus
programs (mostly related to eliminating strictness, since Plutus Core is a
strict language).  Type signatures have also been added to all top-level
functions, but apart from that the original programs have been left unchanged as
much as possible.  Comments relating to the Plutus implementation are delimited
by `{-% ... %-}` and `-- % ...` in order to distinguish them from comments in
the original source.

The Criterion benchmarks use the `plutus-tx` GHC plugin to compile the programs
to Plutus Core and then time their execution on the CEK machine.

The specific programs which we have ported to Plutus are:

   * `clausify`: reduce propositions to clausal form 
   * `knights`: find knight's tours of an NxN chessboard
   * `last-piece`: a solver for a jigsaw problem (not included in the benchmarks)
   * `primetest`: probablisitic primality testing
   * `queens`: find solutions to the N queens problem on an M x M chessboard


Each benchmark can be run with a number of inputs: type

```
  stack bench plutus-benchmark:nofib --ba --list
```

or 
```
  cabal v2-bench plutus-benchmark:nofib --benchmark-arguments --list
```

to see the available benchmarks.

The benchmarks generally take a long time to run, and Criterion has been
configured to run each one for a minimum of 60 seconds in order to get enough
data to get reasonable results (use Criterion's `-L` option to change the
execution time). The `last-piece` program has been omitted from the benchmarkign
process because it exhausts memory on the current version of the CEK machine.

Some of the benchmarks also consume a lot of memory, so it may be helpful to
close memory-hungry programs (Slack, Firefox, ...) before running them.

It's hoped that these benchmarks will be useful for stress-testing Plutus Core
evaluators.  Some of them take a considerable time to run and consume a lot of
memory.  Approximate times for a single execution of each benchmark on the
CEK machine on a 1.6 GHz laptop were as follows:

| Benchmark              | Mean execution time    | Executions per minute  |
|:-----------------------|:-----------------------|:-----------------------|
| clausify/formula1      | 431ms                  | 136                    |
| clausify/formula2      | 540ms                  | 105                    |
| clausify/formula3      | 1.52s                  | 36                     |
| clausify/formula4      | 1.88s                  | 28                     |
| clausify/formula5      | 9.00s                  | 10                     |
| kinghts4x4             | 1.38s                  | 36                     |
| kinghts6x6             | 4.20s                  | 10                     |
| kinghts8x8             | 5.20s                  | 10                     |
| primetest/05digits     | 567ms                  | 91                     |
| primetest/08digits     | 1.10s                  | 45                     |
| primetest/10digits     | 1.60s                  | 36                     |
| primetest/20digits     | 3.43s                  | 15                     |
| primetest/30digits     | 4.96s                  | 10                     |
| primetest/40digits     | 6.48s                  | 10                     |
| primetest/50digits     | out of memory          | -                      |
| queens4x4/bt           | 163ms                  | 354                    |
| queens4x4/bm           | 276ms                  | 276                    |
| queens4x4/bjbt1        | 196ms                  | 301                    | 
| queens4x4/bjbt2        | 202ms                  | 276                    |
| queens4x4/fc           | 459ms                  | 120                    |
| queens5x5/bt           | 2.20s                  | 21                     |
| queens5x5/bm           | 2.41s                  | 21                     |
| queens5x5/bjbt1        | 2.52s                  | 21                     | 
| queens5x5/bjbt2        | 2.58s                  | 21                     |
| queens5x5/fc           | 5.99s                  | 10                     |

The benchmarks were each run with a lower bound for total execution time of 60s,
and the figure in the final column is the total number of times Criterion
executed the relevant benchmark.  One would ideally like hundreds of samples in
order to get useful statistics, so this information may be useful for deciding
which benchmarks to run if, for example, two different versions of the CEK
machine were being compared.  Note also that the total execution time (in
seconds), and hence the number of samples, can be altered with Cirterions `-L`
option.