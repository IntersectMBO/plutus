# plutus-tx: Plutus Tx Haskell support

This provides support for writing Plutus Tx programs in Haskell.

This package just provides support for Plutus Tx, if you are looking for support for
writing smart contracts using Plutus Tx, please look in `plutus-contract`.

NOTE: You will also need `plutus-tx-plugin` as a build dependency so that the
compiler plugin works. If you want to support cross-compilation, see the `plutus-tx-plugin`
`README` for instructions.

## Using `plutus-tx`

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
- Requires access to function definitions
    - Normal function usage requires `INLINEABLE` or `-fexpose-all-unfoldings`
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

Most build tools should work just fine with projects that use `plutus-tx`.

In some circumstances you may need some GHC compiler flags. To be safe, just add all of
- `-fno-ignore-interface-pragmas`
- `-fno-omit-interface-pragmas`
- `-fobject-code`
to all packages that either export functions to be used by the Plutus Tx compiler, or which
use them. These flags should all be harmless, so enabling them is safe.
Further explanation is given below.

### Interface pragmas

The Plutus Tx compiler relies on the bodies of functions being included in the *interface files*
that GHC generates for dependencies. There are two flags that can inhibit this mechanism
and prevent you from using functions from a dependency:
- `-fignore-interface-pragmas` on the *consumer* of a function will prevent it from
  loading the information from the interface files.
- `-fomit-interface-pragmas` on the *producer* of a function will prevent it from
  writing the information to the interface files at all.

These flags are normally only implied by `-O0`, but if you want to support `-O0` (to allow
faster compiles and use in GHCi) then you should disable them explicitly. Depending where the `-O0`
comes from, you may need to explicitly include them in `OPTIONS_GHC` pragmas in the source file
in order to prevent the being overridden.

So on packages that produce functions you should pass `-fno-omit-interface-pragmas`, and
on packages that consume functions you should pass `-fno-ignore-interface-pragmas`.

### Object code

GHCi will use interface files provided you have passed `-fno-ignore-interface-pragmas`
(see above), but the information is designed for object code, not the interpreted bytecode
that GHCi uses by default. To fix this, pass `-fobject-code` for projects using Plutus Tx
which you want to load into GHCi.
