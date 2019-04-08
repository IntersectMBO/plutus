# plutus-tx: PlutusTx Haskell support

This provides support for writing Plutus Tx programs in Haskell using Template Haskell.

This package just provides support for Plutus Tx, if you are looking for support for
writing smart contracts using Plutus Tx, please look in `wallet-api`.

## Haskell language support

In general, most "straightforward" Haskell should work. 

The things that don't work broadly fall into a few categories:
- Not implemented yet
- Incompatible with the design of Plutus Core
- Access to function definitions required
    - This *may* be solved in future
- Use of coercions required
- Assumes "normal" codegen
- Miscellaneous difficult features

In addition, there are some features that do not work but which we plan to support.

Here are a few notable items that do not work:

- Not implemented yet
    - Mutually recursive datatypes
    - Record selectors 
- Incompatible with the design of Plutus Core
    - `PolyKinds`, `DataKinds`, anything that moves towards "Dependent Haskell"
    - Literal patterns
    - `StrictData` and bang patterns (may be allowed in future)
- Access to function definitions required (may be improved in future)
    - Direct use of functions (i.e. not as a TH splice) defined outside the current Plutus Tx expression
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
