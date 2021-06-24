## Plutus contract validation benchmarks

Benchmarks involving a number of validations of transactions
from contracts in `plutus-use-cases`, obtained during the course
of contract execution on the blockchain emulator.

The `data` directory contains validation scripts: see
[the main READMEfile](../README.md) for more information

Note that all of the .plc files in the `data` directory must be mentioned in the
`data-files` section of `plutus-benchmark.cabal` in order to be findable in
`plutus-benchmark/bench-validation/Main.hs`.