---
sidebar_position: 25
---

# Special Functions and Types

Normally, the Plutus Tx compiler compiles a Haskell identifier by obtaining and compiling its definition (also known as unfolding), and creating a term binding in PIR, an intermediate representation used by the Plutus Tx compiler.
Types are compiled in a similar manner, by compiling the type's definition and generating a type or datatype binding in PIR.

However, there are certain special functions and types that aren't compiled this way.
Rather, they are handled specially and directly converted to terms or types in PIR.
It is useful to be aware of these, as these functions and types work differently than regular user-defined functions and types, and cannot be defined in user space.

## Builtin Functions and Types

There are a number of builtin functions and builtin types in UPLC.
The list of builtin functions and types can be found in the [Plutus Core Specification](https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf).

In [`PlutusTx.Builtins.Internal`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Builtins-Internal.html), functions marked `OPAQUE` are directly converted to the corresponding builtin function.
For instance, `PlutusTx.Builtins.Internal.addInteger` is converted to UPLC term `(builtin addInteger)`.
Using the `OPAQUE` pragma prevents GHC from inlining these functions, allowing the Plutus Tx compiler to determine where exactly they are invoked, and compile them appropriately.

Builtin types are handled similarly: rather than compiling their definition, they are directly converted to builtin types in PIR.
In UPLC, most types are erased, but constants remain tagged with the corresponding builtin types.

Since functions in `PlutusTx.Builtins.Internal` correspond to builtin functions that operate on builtin types, it's usually preferable to use functions in [`PlutusTx.Builtins`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Builtins.html).
These functions wrap their counterparts in the `Internal` module, and operate on standard Haskell types whenever possible, which are often more convenient.

Aside from `BuiltinInteger`, which is an alias for `Integer`, other builtin types are distinct from their corresponding Haskell types.
Not all of these Haskell types can be used in Plutus Tx.
For instance, `String` and `ByteString` are not supported, whereas regular algebraic data types like `Bool`, lists and pairs are supported.

## `PlutusTx.Bool.&&` and `PlutusTx.Bool.||`

In [`PlutusTx.Bool`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Bool.html), the `&&` and `||` operators are handled specially in the plugin to ensure they can short-circuit.
In most strict languages, these operators are special and cannot be defined by users, which is also the case for Plutus Tx.

Note that in regular Haskell, `&&` and `||` are _not_ special, as Haskell supports non-strict function applications (and it is the default behavior).

## `IsString` Instances

[`IsString`](https://hackage.haskell.org/package/base/docs/Data-String.html#t:IsString) is a type class from `base`, and can be used along with the `OverloadedStrings` language extension to convert string literals to types other than `String`.

Most `IsString` instances are unsupported by the Plutus Tx compiler, other than a few special cases.
At present, it provides support for `BuiltinString` and `BuiltinByteString`, with the caveat that the `fromString` method must be applied to a string literal.

As previously noted, `String` and `ByteString` are not available in Plutus Tx, so you'll need to use `BuiltinString` or `BulitinByteString`.
This lets you write `"hello" :: BuiltinString` and `"world" :: BuiltinByteString` in Plutus Tx, which is quite convenient.
