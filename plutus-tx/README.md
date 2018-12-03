# plutus-tx: PlutusTx Haskell support

This provides support for writing PlutusTx programs in Haskell using Template Haskell.

This package just provides support for PlutusTx, if you are looking for support for
writing smart contracts using PlutusTx, please look in `wallet-api`.

## Haskell language support

In general, most "straightforward" Haskell should work. More advanced features may
or may not work, depending on whether they rely on features of GHC Core that aren't
supported. Most syntactic language extensions should be fine, you may get into trouble
with more advanced type system extensions.

TODO: link to GitHub issues for planned items once we're using them.

Not supported, but support planned:
- Mutually recursive datatypes (support planned)
    - Self-recursive datatypes are supported
- Record selectors (support planned)
- Functions defined outside the PlutusTx expression

Not supported, and support not planned:
- Datatypes beyond simple "Haskell98" datatypes
    - GADTs, constrained constructors, etc.
- Abstract datatypes
- Numeric types other than `Int`
- Literal patterns
- Typeclasses
    - Some `Num`, `Eq`, and `Ord` methods on
      `Int` and `Bytestring` are supported specially.
- Anything involving coercions

## Tutorial

See [here](tutorial/Tutorial.md) for a tutorial.
