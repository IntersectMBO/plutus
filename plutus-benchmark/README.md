# Plutus Benchmarks

## Implementation note

When implementing evaluation benchmarks, make sure to use 'mkEvalCtx' and
'evaluateCekForBench' to mimic the behavior of the ledger. If you use something
else for evaluation, the results are likely not going to be representative of
what actually happens in production.

## Benchmark suites

This directory contains four sets of benchmarks:

### `nofib`

Plutus versions of some of Haskell's `nofib` benchmarks from https://github.com/ghc/nofib.

These programs are not representative of the kind of code that gets run on the chain and mostly
serve as a check that the evaluator can handle long-running and memory-intensive
computations.

* The source for the individual programs is in `nofib/src`
* There is an executable in `nofib/exe` which can be used to run the individual programs (compiled into Plutus)
* The benchmarking code is in `nofib/bench`.

* To run the benchmarks using cabal, type a command like this
  * `cabal bench plutus-benchmark:nofib` (run all benchmarks; this will take a long time)
  * `cabal run plutus-benchmark:nofib` (runs the benchmarks with the working directory set to the shell's current working directory. `cabal bench` sets the working directory to the `plutus-benchmark` directory.)

  * `cabal run plutus-benchmark:nofib -- clausify/formula2 -L300` (run the `clausify/formula2` benchmark with a time limit of 300 seconds. By default, the `nofib` benchmarks are run for a minimum of **60 seconds
    each** in order to get a statistically reasonable number of executions.
    You can change this with Criterion's `-L` option.  With the 60 second limit
    the entire suite takes perhaps 20-40 minutes to run (although this will
    depend on the hardware))
  * `cabal bench plutus-benchmark:nofib --benchmark-options "clausify/formula2 -L300"` (similar to above)

See also [nofib/README.md](./nofib/README.md).

### `validation`

A number of Plutus Core scripts that are representative for on-chain validators.

These scripts were originally written in Plinth and then compiled. They are
stored in `validation/data` in serialised form, so that changes in the compiler
wont't affect the resulting UPLC and skew the execution benchmarks. The sources
are not part of the repo anymore (the original code can be browsed here:
[`plutus-use-cases/`](https://github.com/IntersectMBO/plutus/tree/942bd8c6de6a2d5981d91c704b0258bddd9d9d7c/plutus-use-cases)
.

The serialised scripts can therefore no longer be generated from source and
should not change. See note `Original generation of the .flat files` how they
were generated.

* The scripts are stored in flat-encoded form in various subdirectories of `validation/data`.

* The benchmarking code is in `validation/Main.hs`.

* To run the benchmarks using cabal, type a command like this
    * `cabal bench plutus-benchmark:validation` or `cabal run plutus-benchmark:validation` (run all benchmarks)
    * `cabal run plutus-benchmark:validation -- crowdfunding/2 -L60` (run the `crowdfunding/2`
        benchmark with a time limit of 60 seconds)

* During benchmarking each validation script is run repeatedly up to a limit
  of 20 seconds (a single execution takes approximately 5-15 ms) to get
  statistically reasonable total number of executions.  It takes about 10
  minutes to run the entire suite (again, this will depend on the hardware).

* There are also two variants (`validation-decode` & `validation-full` ) that measure
  the performance of the validation dataset for the script deserialization,
  and for the deserialization and extra checks and execution, respectively.

See also [validation/README.md](./validation/README.md).

### `lists`

Some simple algorithms on lists.  See [lists/README.md](./lists/README.md) for more information.
noi 
### `marlowe`

* The source for a minimal version of the Marlowe validators is in `marlowe/src`.
* There is an executable in `marlowe/exe` which can be used to run benchmarks for a set of scripts.
* The benchmarking code is in `marlowe/bench`.

* To run the benchmarks using cabal, type a command like this
    * `cabal bench plutus-benchmark:marlowe` or
    * `cabal run plutus-benchmark:marlowe`

See also [marlowe/README.md](./marlowe/README.md).

## Executables
The `nofib-exe` program in `nofib/exe` allows you to run the `nofib` benchmarks from the command line and
output Plutus Core versions in a number of formats.  See the built-in help information
for details.

For `marlowe`, the `marlowe-validators` program allows you to run benchmarks in certain folders and get a summary of results. See the [marlowe/README.md](./marlowe/README.md) for details.

## Criterion output

The benchmarks will generate a file called `report.html` containing
detailed information about the results of running the benchmarks. This will be
written to the `plutus-benchmark` directory.  To put it elsewhere, pass
Criterion the `--output` option along with an *absolute* path (relative paths
are interpreted relative to `plutus-benchmark` when running the benchmarks via
cabal): for example

```
  cabal run plutus-benchmark:validation -- crowdfunding -L60 --output $PWD/crowdfunding-report.html
```

`cabal run` will write the output into
the current directory (unless you use `cabal run <benchmark> -- --output ...`).

The `templates` directory contains a template file for use by Criterion: this extends
the HTML report to include the total number of times each benchmark was run and the
total amount of time spent running each benchmark.

## Tests

The directory `nofib/test` contains some tests for the nofib examples which
compare the result of evaluating the benchmarks as Haskell programs and as
Plutus Core programs.  Run these with `cabal test plutus-benchmark`.
