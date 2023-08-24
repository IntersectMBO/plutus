
<a id='changelog-1.11.0.0'></a>
# 1.11.0.0 — 2023-08-24

## Added

- Add a new PlutusTx compiler option, `dump-compilation-trace`. It can be used to dump
  the full trace of compiling GHC `CoreExpr`s into PIR `Term`s for debugging.

## Fixed

- The plugin could generate exponentially large code from nested pattern matches with many default cases.
  This could happen when using pattern synonyms. This no longer happens.

<a id='changelog-1.8.0.0'></a>
# 1.8.0.0 — 2023-06-22

## Added

- New built-in types and functions for BLS12-381 operations.

<a id='changelog-1.7.0.0'></a>
# 1.7.0.0 — 2023-05-22

## Added

- GHC 9.6 support

<a id='changelog-1.6.0.0'></a>
# 1.6.0.0 — 2023-05-04

## Added

- `target-version` option that allows you to choose the target PLC version for the generated code.

<a id='changelog-1.3.0.0'></a>
# 1.3.0.0 — 2023-03-08

## Added

- `INLINE` pragmas from Haskell source are now propagated to Plutus IR, so they are guaranteed to be inlined.
