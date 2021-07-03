# plutus-pab tests

There are two test suites in `plutus-pab.cabal`:

* `plutus-pab-test-full` has the main PAB tests (for `Plutus.PAB.Core` and related modules). It depends on `plutus-use-cases`.
* `plutus-pab-test-light` has some tests that don't depend on `plutus-use-cases`