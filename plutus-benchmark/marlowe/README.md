# Experimental version of Marlowe validator for Cardano, with minimal dependencies

## `marlowe-internal`

This package is a fully representative version of the Marlowe validator on chain, currently. (See the "Managing versions" section below) It is primarily for benchmarking/profiling Marlowe scripts. 

Marlowe is a platform for financial products as smart contracts. [Marlowe-Cardano](https://github.com/input-output-hk/marlowe-cardano) is an implementation of Marlowe for the Cardano blockchain, built on top of Plutus.

In short, users write a Marlowe application in `Marlowe-Cardano`, which generates the corresponding code that is ready for the Plutus compiler with some manual revision. The code then goes through the Plutus compiler pipeline and gets executed on Cardano.

The Plutus Core team has been working on optimizing the compiler such that a script's budget is reduced. The budget is a reflection of

(1) script sizes
(2) execution costs

It would be informative for both the Plutus and Marlowe teams to investigate in detail how the Marlowe scripts can be optimized. In particular, we can perform:

(1) Benchmarking: compare the budget before and after optimizations that the Plutus team implemented. It could be helpful to do the benchmarking *as* we implement the optimization even.

The benchmarking portion of the code lives in `marlowe/bench`(TODO), which depends on this package.

(2) Profiling: look at each script in more detail, what functions are taking up the most budget? How can they be optimized?

See [CONTRIBUTING.md](https://github.com/input-output-hk/plutus/blob/master/CONTRIBUTING.adoc#how-to-build-the-code-with-profiling) for profiling instructions.

Of the most common Marlowe transactions, input application transactions are the most relevant, as they are complex and can go over the execution limits at times. So there is a priority on examining those contracts.

## Managing versions

### Versioning of this package 

Note that the off-chain code is evolving. However the on-chain code is very stable and is compatible with GHC 8.10.7. For best benchmarking results, eventually we may have to update some of these files by hand if the on chain code is updated. (We don't want to depend on the Marlowe repository because this will have the problem of circular dependency.)

### Script versions

The production version of Marlowe currently uses (PlutusV2, vasilPV, plcVersion100 or 1.0.0). We should use the same combination in the benchmarking.

For documentation on Plutus vs PLC vs protocol version, see [here](https://github.com/input-output-hk/plutus/blob/master/plutus-ledger-api/src/PlutusLedgerApi/Common/Versions.hs)

## Running the benchmarks with executable `marlowe-validators`

The application `marlowe-validators` works with scripts in the `plutus-benchmark/marlowe/exe/scripts/rolepayout` and `plutus-benchmark/marlowe/exe/scripts/semantics` directories. It serialises the two Marlowe validator scripts, computes their hashes, and runs all of the benchmarks, storing the results in a pair of tab-separated-value files.

In `plutus-benchmark/marlowe/src/Language/Marlowe/Scripts.hs`, the plugin option to dump Plutus programs is turned on. Therefore, running the executable dumps the initial and simplified PIR program and the typed and untyped PLC program. You can find them in the `plutus/plutus-benchmark` directory. The dumped files are named with the module name followed by a brief description and ".flat".

Running `cabal run marlowe-validators` outputs the following files:

- For Marlowe's semantics validator
    - Plutus script: `marlowe-semantics.plutus`
    - Benchmarking results: `marlowe-semantics.tsv`   
    - Flat UPLC files: `benchmarks/semantics/*-uplc.flat`
- For Marlowe's role-payout validator
    - Plutus script: `marlowe-rolepayout.plutus`
    - Benchmarking results: `marlowe-rolepayout.tsv`   
    - Flat UPLC files: `benchmarks/rolepayout/*-uplc.flat`