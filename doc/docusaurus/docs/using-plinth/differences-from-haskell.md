---
sidebar_position: 15
---

# Differences From Haskell

## Strictness

### Function Applications

Unlike in Haskell, function applications in Plinth are strict.
In other words, when evaluating `(\x -> 42) (3 + 4)` the expression `3 + 4` is evaluated first, before evaluating the function body (`42`), even though `x` is not used in the function body.

Using lazy patterns on function parameters does not change this behavior: `(\(~x) -> 42) (3 + 4)` still evaluates `3 + 4` strictly.
At this time, it is not possible to make function applications non-strict in Plinth.

### Bindings

Bindings in Plinth are by default non-strict, but they can be made strict via the bang pattern (`!`), as in `let !x = 3 + 4 in 42`.
Conversely, in modules with the `Strict` language extension on, bindings are by default strict, but they can be made non-strict via the lazy pattern (`~`), as in `let ~x = 3 + 4 in 42`.

> :pushpin: **NOTE**
>
> It is important to note that the UPLC evaluator does not perform lazy evaluation, which means a non-strict binding will be evaluated each time it is used, rather than at most once.

## Supported Haskell Features

The Plinth compiler provides good support for basic Haskell features, including regular algebraic data types, type classes, higher order functions, parametric polymorphism, etc.
However, it doesn’t support many of Haskell’s more advanced features.
A good rule of thumb for writing Plinth is to stick with simple Haskell (which is also typically good advice for Haskell development in general).

## Unsupported Haskell Features

Some notable Haskell features _not_ supported by Plinth include:

- Many functions and methods in [`base`](https://hackage.haskell.org/package/base).
  Use the counterparts in the [`plutus-tx`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/) library instead.
  This also means most Haskell third-party libraries are not supported, unless the library is developed specifically for Plinth.
- Mutually recursive data types.
- Type families
- Existential types
- GADTs
- IO and FFI

Use of these features often leads the Plinth compiler to report an "Unsupported feature" error, though you may sometimes get a different error.

Since the Plinth compiler is a GHC plugin that runs after GHC's type checking, unsupported Haskell features cannot be detected at type checking time.
As a result, it's unlikely that an IDE will be able to report these errors.
You will need to compile the Haskell module to determine if everything is compiled successfully.
