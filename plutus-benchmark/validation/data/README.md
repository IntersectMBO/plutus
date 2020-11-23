## Scripts for Plutus contract validation benchmarks

This directory contains source code for Plutus Core scripts involved in
validation in the `plutus-use-cases` tests.  The validators, datum scripts,
redeemers and contexts have all been extracted into separate files.  In the
tests, some of the scripts appear in mulitple validations and some validations
occur multiple times. Only a single copy of each script has been kept: each
subdirectory has a README file explaining which scripts are involved in each
validation.

Note that all of the .plc files in this directory must be mentioned in the
`data-files` section of `plutus-benchmark.cabal` in order to be findable in
`plutus-benchmark/bench-validation/Main.hs`.