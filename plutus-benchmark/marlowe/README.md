# Experimental version of Marlowe validator for Cardano, with minimal dependencies

The `marlowe` directory contains four components:

- Validator source code: `marlowe-internal`
- Benchmarking: `marlowe`
- Executable: `marlowe-validators`
- Budget tests: `plutus-benchmark-marlowe-tests`

## `marlowe-internal`

This library is a fully representative version of the Marlowe validator on chain, currently. (See the "Managing versions" section below) It is primarily for measuring budgets/performance of Marlowe scripts. 

Marlowe is a platform for financial products as smart contracts. [Marlowe-Cardano](https://github.com/input-output-hk/marlowe-cardano) is an implementation of Marlowe for the Cardano blockchain, built on top of Plutus.

In short, users write a Marlowe application in `Marlowe-Cardano`, which generates the corresponding code that is ready for the Plutus compiler with some manual revision. The code then goes through the Plutus compiler pipeline and gets executed on Cardano.

The Plutus Core team has been working on optimizing the compiler such that a script's budget is reduced. The budget is a reflection of

(1) script sizes
(2) execution costs

It would be informative for both the Plutus and Marlowe teams to investigate in detail how the Marlowe scripts can be optimized. In particular, we can perform:

(1) Benchmarking: compare the budget before and after optimizations that the Plutus team implemented. It could be helpful to do the benchmarking *as* we implement the optimization even.

The benchmarking portion of the code lives in `marlowe/bench`, which depends on this library.

(2) Profiling: look at each script in more detail, what functions are taking up the most budget? How can they be optimized?

See [CONTRIBUTING.md](https://github.com/input-output-hk/plutus/blob/master/CONTRIBUTING.adoc#how-to-build-the-code-with-profiling) for profiling instructions.

Of the most common Marlowe transactions, input application transactions are the most relevant, as they are complex and can go over the execution limits at times. So there is a priority on examining those contracts.

## Benchmarking with `marlowe`

To benchmark the Marlowe scripts, run `cabal bench marlowe`. 

The default time for each benchmark to run is 5 seconds. One can change this with `-L` or `--timeout` when running it locally. For each benchmark Criterion runs it as many times as it can within the `-L` argument and then analyses the collected results to get the mean time and the standard deviation and so on. If you've got a long-running benchmark then you might want to increase the timeout to get more accurate statistics. The default is kept low to not overload our benchmarking machine.

The scripts are the results of applying the script's datum, redeemer and context, taken from files of type `M.Benchmark` from `/marlowe/scripts`, which is a data type in `marlow-internal`. This is not to be confused with `criterion`'s [`Benchmark`](https://hackage.haskell.org/package/criterion-measurement-0.2.1.0/docs/Criterion-Measurement-Types.html#t:Benchmark) type. 

`M.Benchmark` also contains the execution costs, measured using the Plutus version on August 18 2022 (commit 6ed578b592f46afc0e77f4d19e5955a6eb439ba4). This is used by the executable.

There are two sets of scripts: semantics (in `/marlowe/scripts/semantics`) and role payout (in `/marlowe/scripts/rolepayout`). The benchmark prints the transaction IDs of each script. 

## Running the benchmarks with executable `marlowe-validators`

The application `marlowe-validators` works with scripts in the `plutus-benchmark/marlowe/scripts/rolepayout` and `plutus-benchmark/marlowe/scripts/semantics` directories. It serialises the two Marlowe validator scripts, computes their hashes, and runs all of the benchmarks, storing the results in a pair of tab-separated-value files.

Running `cabal run marlowe-validators` outputs the following files:

- For Marlowe's semantics validator
    - Plutus script: `marlowe-semantics.plutus`
    - Benchmarking results: `marlowe-semantics.tsv`   
    - Flat UPLC files: `benchmarks/semantics/*-uplc.flat`
- For Marlowe's role-payout validator
    - Plutus script: `marlowe-rolepayout.plutus`
    - Benchmarking results: `marlowe-rolepayout.tsv`   
    - Flat UPLC files: `benchmarks/rolepayout/*-uplc.flat`

## Running the budget tests

To run the budget tests for Marlowe scripts, run `cabal test plutus-benchmark-marlowe-tests`. 

Similar to the benchmarking, the budget tests use two sets of scripts: semantics (in `/marlowe/scripts/semantics`) and role payout (in `/marlowe/scripts/rolepayout`). The test names are the transaction IDs of each script.

The golden files contain the counted CPU and memory budget of the scripts.

## Managing versions

### Versioning of `marlowe-internal`

Note that the off-chain code is evolving. However the on-chain code is very stable and is compatible with GHC 8.10.7. For best benchmarking results, eventually we may have to update some of these files by hand if the on chain code is updated. (We don't want to depend on the Marlowe repository because this will have the problem of circular dependency.)

### Script versions

The production version of Marlowe currently uses (PlutusV2, vasilPV, plcVersion100 or 1.0.0). We should use the same combination in the benchmarking. Again we should make sure this is synced up.

For documentation on Plutus vs PLC vs protocol version, see [here](https://github.com/input-output-hk/plutus/blob/master/plutus-ledger-api/src/PlutusLedgerApi/Common/Versions.hs)
