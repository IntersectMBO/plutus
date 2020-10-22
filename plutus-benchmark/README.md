## Plutus Benchmarks

This directory contains two sets of benchmarks:

* `nofib`: Plutus versions of some of Haskell's `nofib` benchmarks from https://github.com/ghc/nofib.

   * The source for the individual programs is in `nofib/src`
   * There is an executable in `nofib/exe` which can be used to run the individual programs (compiled into Plutus)
   * The benchmarking code is in `nofib/bench`.

   * To run the benchmarks using stack, type a command like this
       * `stack bench plutus-benchmark:nofib` (run all benchmarks; this will take a long time)
       * `stack bench plutus-benchmark:nofib --ba "clausify/formula2 -L300"` (run the `clausify/formula2`
          benchmark with a time limit of 300 seconds)

   * The corresponding cabal commands are
       * `cabal v2-bench plutus-benchmark:nofib`
       * `cabal v2-bench plutus-benchmark:nofib --benchmark-options "clausify/formula2 -L300"``

* `validation`:  a number of Plutus Core scripts extracted from the `plutus-use-cases` tests which represent realistic on-chain
   transaction validations.

   * The scripts are stored as Plutus Core source in `validation/data`, along with a description
     of how to combine them to obtain executable applied validators.
   * Benchmarking code is stored in `validation/Main.hs`.

   * To run the benchmarks using stack, type a command like this
       * `stack bench plutus-benchmark:validation` (run all benchmarks)
       * `stack bench plutus-benchmark:validation --ba "crowdfunding/2 -L10"` (run the `crowdfunding/2`
           benchmark with a time limit of 10 seconds)
   * The corresponding cabal commands are
       * `cabal v2-bench plutus-benchmark:validation`
       * `cabal v2-bench plutus-benchmark:validation --benchmark-options "crowdfunding/2 -L10"`

See also  [nofib/README.md](./nofib/README.md)  and [validation/README.md.](./validation/README.md).

### Criterion output

Both sets of benchmarks will generate a file called `report.html` containing
detailed information about the results of running the benchmarks. This will be
written to the `plutus-benchmarks` directory.  To put it elsewhere, pass
Criterion the `--output` option along with an *absolute* path (relative paths
are interpreted relative to `plutus-benchmarks` when running the benchmarks via
satck or cabal): for example

```
  stack bench plutus-benchmark:validation --ba "crowdfunding -L10 --output $PWD/crowdfunding-report.html"
```

The `templates` directory contains some template files for use by Criterion.
