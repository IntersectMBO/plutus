
<a id='changelog-1.12.0.0'></a>
# 1.12.0.0 — 2023-09-01

## Changed

- The `Strict` extension is now on by default in all of Plutus Tx.

<a id='changelog-1.10.0.0'></a>
# 1.10.0.0 — 2023-08-02

## Added

- Haskell function for `keccak_256` builtin
- Haskell function for `blake2b_224` builtin

<a id='changelog-1.8.0.0'></a>
# 1.8.0.0 — 2023-06-22

## Added

- New built-in types and functions for BLS12-381 operations.

<a id='changelog-1.7.0.0'></a>
# 1.7.0.0 — 2023-05-22

## Added

- GHC 9.6 support

## Changed

- Monomorphized functions in PlutusTx.Foldable that should short-circuit.
  This makes them short-circuit properly.

- `liftCode` and some other functions in `PlutusTx.Lift` now return PIR in addition to UPLC.

<a id='changelog-1.6.0.0'></a>
# 1.6.0.0 — 2023-05-04

## Changed

- Various `Lift` functions gained `Version` arguments, so that you can control the version of PLC used in the resulting program. This also affects how the PIR compiler will compile datatypes.

<a id='changelog-1.4.0.0'></a>
# 1.4.0.0 — 2023-03-23

## Added

- `unsafeApplyCode`, a variant of `applyCode` that throws if the language versions don't match.

## Changed

- `applyCode` now requires matching Plutus Core language versions.

<a id='changelog-1.3.0.0'></a>
# 1.3.0.0 — 2023-03-08

## Removed

- Removed Plutus Tx library functions with the `Haskell.Monad` constraint.
  Functions requiring `Functor` and `Applicative` are using `PlutusTx.Functor` and
  `PlutusTx.Applicative`, but those requiring `Monad` were using Haskell's `Monad`, which
  is inconsistent and confusing. We should either add a `PlutusTx.Monad` class, or switch
  to Haskell's `Functor` and `Applicative`. Some of these functions like `sequence_` and
  `mapM_` are also not useful, and one should prefer `sequenceA_` and `traverse_`, respectively.

## Changed

- Use `foldr` instead of `foldMap` in `PlutusTx.Foldable`
