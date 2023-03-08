### Removed

- Removed Plutus Tx library functions with the `Haskell.Monad` constraint.
  Functions requiring `Functor` and `Applicative` are using `PlutusTx.Functor` and
  `PlutusTx.Applicative`, but those requiring `Monad` were using Haskell's `Monad`, which
  is inconsistent and confusing. We should either add a `PlutusTx.Monad` class, or switch
  to Haskell's `Functor` and `Applicative`. Some of these functions like `sequence_` and
  `mapM_` are also not useful, and one should prefer `sequenceA_` and `traverse_`, respectively.
