# plutus-tx: Plutus Tx Haskell support

This provides support for writing Plutus Tx programs in Haskell.

This package just provides support for Plutus Tx, if you are looking for support for
writing smart contracts using Plutus Tx, please look in `plutus-wallet-api`.

## Using `plutus-tx`

More extensive tutorials are available in `plutus-tutorial`.

### Compiling Haskell code

The entry point is the `compile` function, which takes a typed Template Haskell
quote and compiles it into a Plutus Tx program (represented as a `CompiledCode`) at
Haskell compilation time.

### Lifting Haskell values at runtime

Haskell values can be lifted into code at runtime using the `lift` functions.

Instances of the `Lift` typeclass should be created only with the `makeLift` Template Haskell
function.

Lifting can be used to pass values to compiled Plutus Tx programs using `applyCode`.

## Haskell language support

In general, most "straightforward" Haskell should work.

The things that don't work broadly fall into a few categories:

- Not implemented yet
    - Mutually recursive datatypes
- Incompatible with the design of Plutus Core
    - `PolyKinds`, `DataKinds`, anything that moves towards "Dependent Haskell"
    - Literal patterns
    - `StrictData` and bang patterns (may be allowed in future)
- Requires access to function definitions
    - Normal function usage requires `INLINEABLE` in some circumstances
    - Typeclass dictionaries
- Use of coercions required
    - GADTs
    - `Data.Coerce`
    - `DerivingVia`, `GeneralizedNewtypeDeriving`, etc.
- Assumes "normal" codegen
    - FFI
    - Numeric types other than integers
    - `MagicHash` types
    - Machine words, C strings, etc.
- Miscellaneous difficult features

## Building projects with `plutus-tx`

Most build tools should work just fine with projects that use `plutus-tx`. However,
if you want to use it in a project you are *intepreting* (e.g. loading into GHCI, using
doctest), then you need to compile with `-fobject-code`.

If you are not interpreting code and you find it complains that functions are not `INLINABLE`,
you may need `-fno-ignore-interface-pragmas`.
