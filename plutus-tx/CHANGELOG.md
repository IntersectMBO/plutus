
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
