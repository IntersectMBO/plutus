## Changed

- Constant universes are indexed by fully instantiated Haskell types. `DefaultUniList`, `DefaultUniPair`, and `DefaultUniArray` are direct constructors; `Esc`, `Kinded`, `DefaultUniApply`, and the prototype constructors are removed. Constant decoding reads tags directly from the Flat bit stream, without an intermediate tag list or runtime kind checking, preserving the existing value-decoder sharing optimizations.
- `TyBuiltin` stores the separate `SomeTypeHead` data family, with a finite head enum for `DefaultUni`. Applications use `TyApp`. `KnownTypeHead` reifies Haskell heads, and `mkTyBuiltinOf` uses `KnownTypeAst` to construct complete types.
- Existential constant tags use the existing `Some` wrapper; `SomeTypeIn` is removed. `decodeUni` reads `Word8` tags directly from the Flat bit stream.
- `HasUniApply`, `matchUniApply`, `uniApply`, `tryUniApply`, `foldUni`, and the inverse type-to-tag conversion are removed. Normalization and normality checking no longer need a universe constraint; the `MonadNormalizeType` alias is removed in favor of `MonadQuote`.
- Parsers expand applied built-in types into `TyApp` nodes. Typed Flat serializes heads and applications directly; constant and UPLC encodings are unchanged.
- `KnownKind` reifies Plutus kinds directly; the singleton-kind wrappers and their conversion helpers are removed.
- The universe parameter of the type AST and `CompiledCodeIn` has nominal role because type heads use a data family.
