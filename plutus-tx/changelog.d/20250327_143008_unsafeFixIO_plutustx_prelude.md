
### Changed

- `PlutusTx.Prelude` no longer re-exports `PlutusTx.List`. There are now two separate
  list modules: `PlutusTx.List` and `PlutusTx.Data.List`. Pick the one that fits your
  use case and import it explicitly.

- `PlutusTx.Prelude` no longer re-exports `PlutusTx.Foldable` or `PlutusTx.Traversable`.
  These typeclasses are generally discouraged due to their performance overhead.
  For example, instead of using `PlutusTx.Foldable.foldMap`, consider rewriting
  your code using `PlutusTx.List.foldr`.

- `PlutusTx.Prelude` now re-exports `BuiltinBool`, `BuiltinList`, `BuiltinPair`,
  `ToData`, `FromData` and `UnsafeFromData`.
