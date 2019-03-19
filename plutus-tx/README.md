# plutus-tx: PlutusTx Haskell support

This provides support for writing Plutus Tx programs in Haskell using Template Haskell.

This package just provides support for Plutus Tx, if you are looking for support for
writing smart contracts using Plutus Tx, please look in `wallet-api`.

## Haskell language support

In general, most "straightforward" Haskell should work. 

The things that don't work broadly fall into a few categories:
- Not implemented yet
- Incompatible with the design of Plutus Core
- Requires access to function definitions 
    - Normal function uage requires `INLINEABLE` in some circumstances (external packages)
    - Typeclass dictionaries
- Use of coercions required
- Assumes "normal" codegen
- Miscellaneous difficult features

In addition, there are some features that do not work but which we plan to support.

Here are a few notable items that do not work:

- Not implemented yet
    - Mutually recursive datatypes
- Incompatible with the design of Plutus Core
    - `PolyKinds`, `DataKinds`, anything that moves towards "Dependent Haskell"
    - Literal patterns
    - `StrictData` and bang patterns (may be allowed in future)
- Access to function definitions required (may be improved in future)
    - Typeclasses (dictionary construction)
- Use of coercions required
    - GADTs
    - `Data.Coerce`
    - `DerivingVia`, `GeneralizedNewtypeDeriving`, etc.
- Assumes "normal" codegen
    - FFI
    - Numeric types other than integers
    - `MagicHash` types
    - Machine words, C strings, etc.
