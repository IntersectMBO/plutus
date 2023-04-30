# ADR 5: Plutus Tx's Evaluation Strategy, Compiler and Standard Library

Date: 2023-04

## Authors

Ziyang Liu <ziyang.liu@iohk.io>

## Status

Proposed

## Background

Plutus Tx is a language for writing Plutus scripts.
It is a subset of Haskell and can be compiled to Untyped Plutus Core (hereafter referred to as PLC) by the Plutus Tx compiler, a GHC plugin.

Haskell is a non-strict language that uses the call-by-need evaluation strategy (lazy evaluation) by default, while PLC is strict and uses call-by-value.
This begs the question: what is the evaluation order and evaluation strategy of Plutus Tx?
This is an important question, the answer of which not only dictates how users of Plutus Tx should reason about and optimize their programs, but also has major implications on the design and implementation of the Plutus Tx compiler and libraries.

Unfortunately, this question is currently difficult to answer.
Note that there are only two possible evaluation strategies for Plutus Tx: (strict evaluation, call-by-value) and (non-strict evaluation, call-by-name).
In parcitular, Plutus Tx cannot use call-by-need because PLC's evaluator (the CEK machine) has no support for thunks and memoization.
What is unclear is whether Plutus Tx is strict or non-strict.
Indeed, it is sometimes strict and sometimes non-strict, and it is fairly random and difficult to predict:

- Let-bindings in Plutus Tx are by default non-strict, but function applications are strict.
  That is, `let x = rhs in body` isn't equivalent to `(\x -> body) rhs`.
  This is distinct from most other languages, regardless of their evaluation orders and evaluation strategies, in which these two expressions are equivalent.

- The conditional expression `if b then t else f` is always non-strict in `t` and `f`, like in most strict languages.
  But what about `foo b t f = if b then t else f`? In a strict language, `foo` would be strict, and in a non-strict language, it would be non-strict.
  But in Plutus Tx, due to how its compiler is currently implemented, whether `t` and `f` are evaluated strictly or not depends on whether GHC inlines `foo`.
  Although we turn off GHC's inliner in the Plutus Tx compiler, GHC may still decide to unconditionally inline `foo` if it is used only once.
  In general, it is not easy to predict whether GHC will inline something or not.

The lack of consistency makes it difficult to reason about the efficiency of Plutus Tx programs, and difficult to write useful libraries for Plutus Tx that guarantee to have the desirable behaviors (e.g., short-circuiting).

This ADR proposes a few changes to the Plutus Tx language and the compiler to make the semantics more predictable.
It also proposes changes to the Plutus Tx standard library to make it more performant.

## Proposed Changes

Plutus Tx should be a strict-by-default language, mainly because it cannot currently use call-by-need (lazy) evaluation.
If it was non-strict by default, call-by-name evaluation would be the default evaluation strategy.
Call-by-name is rarely used in practice since it leads to repeated evaluations.
Unless we implement call-by-need evaluation for PLC in the future, strictness should be the default for Plutus Tx.
Given this, the following changes are proposed.

### Making Let-bindings Strict By Default

In a strict language, it would make sense that let-bindings be strict by default, since that's what almost all strict languages do.
Plus, non-strict bindings should be used cautiously in a language that adopts call-by-name (which is the only possible way to evaluate non-strict bindings in Plutus Tx), since they can easily lead to an unbounded amount of repeated evaluation.
But if make let-bindings strict by default, then the question is, how does one make a non-strict let-binding?

Haskell supports irrefutable patterns with the `~` operator, and it can be used on let-bindings, e.g., `let ~x = rhs`. So one possibility is to make non-strict let-bindings this way.
However, irrefutable patterns have no effect on simple pattern bindings (i.e., the pattern is a single variable), and it makes no difference in GHC Core, which means the Plutus Tx compiler can't actually see the `~`.
It is technically possible to make `~` work but it would require adding a GHC parser plugin to capture `~` in GHC Core, among other things, adding a great deal of complexity.

This is the reason why let-bindings have been non-strict by default in Plutus Tx, and creating strict let-bindings requires using bang patterns.

We have a few options:

1. Do nothing, and encourage people to use the `Strict` GHC extension, which makes     let-bindings strict by default.
   This is not technically "strict by default", since the `Strict` extension is off by default, but it is still ergonomically better than using bang patterns on every binding.

   One argument against this is that a module may contain both on-chain and off-chain code, some modules contain off-chain code only, and the same piece of code may be both on-chain and off-chain.
   For off-chain code one typically doesn't want to enable `Strict`.
2. Enable `Strict` automatically.
   This can be done in a GHC driver plugin.
   But like said in Option 1, one doesn't usually want to enable `Strict` on off-chain code.
   Thus at the very least, we'd need to provide the option to turn it off via `NoStrict`, and this is tricky to implement.
3. Introduce the following function:

  ```haskell
  nonstrict :: forall a. a -> a
  nonstrict = id
  {-# NOINLINE nonstrict #-}
  ```

  Then, to create a non-strict let-binding, we write

  ```haskell
  let x = nonstrict rhs in body
  ```

  Because of the NOINLINE pragma, `nonstrict` is guaranteed to be visible to the Plutus Tx compiler.
  Whenever the Plutus Tx compiler sees `let x = nonstrict rhs`, it first compiles `rhs` normally; then it creates a nonstrict binding in PIR: `let ~x = rhs_compiled`.

The advantages of making let-bindings strict by default, and using `nonstrict` for non-strict bindings are:

- It makes it more convenient, rather than less convenient, to create strict bindings than non-strict bindings, which is what a strict language should do.
- It works for both on-chain code and off-chain code. A let-binding is strict by default when used in on-chain code, and non-strict by default otherwise.

The disadvantages are:

- It is a magic function that needs special support in the Plutus Tx compiler.
- This is a critical one: it is susceptible to GHC inlining bindings unconditionally.
  If GHC decides to turn `let x = rhs in ...x...` into `...rhs...`, then `x` effectively becomes non-strict, and there's nothing the Plutus Tx compiler can do to recover `x`.

If we can modify the Plutus Tx compiler such that we can turn off GHC's pre-inliner (which will be discussed later), then option 3 becomes the most preferrable.
Otherwise option 3 doesn't really work and we'll have to go with option 1.

### Defining non-strict functions

In Plutus Tx, like most other strict languages, only a few built-in constructs are non-strict (such as if-then-else).
It is often cumbersome, if not impossible, to create user-defined non-strict functions.

It would be useful to allow user-defined non-strict functions, so that we can define functions like `&&` and `||` that short-circuit properly.
Some languages like Scala have special syntaxes for defining non-strict functions; we can't change Haskell's syntax, so we need to find a different solution.

The idea is to make the Plutus Tx compiler perform inlining and beta reduction for functions with INLINE pragmas, i.e., the same as how GHC treats INLINE pragmas.

Note that "beta reduction" here refers to beta reduction traditionally defined for lambda calculus, i.e., `((\x. body) rhs) -> body [x := rhs]`, rather than the beta reduction [implemented in PIR](https://github.com/input-output-hk/plutus/blob/daad7f7a5962c63bd01db8262f1cf57df6603ef6/plutus-core/plutus-ir/src/PlutusIR/Transform/Beta.hs).
The latter creates a strict variable from the argument, i.e., `((\x. body) rhs) -> let !x = rhs in body`.
In the following, we refer to the former as _beta substitution_ for disambiguation.

As an example, consider the definition of `(&&)`:

```haskell
(&&) :: Bool -> Bool -> Bool
a && b = if a == False then False else b
{-# INLINE && #-}
```

Normally when the Plutus Tx compiler inlines `(&&)` and performs beta reduction, `expr1 && expr2` becomes

```haskell
let !x = expr1
    !y = expr2
 in if x == False then False else y
```

whereas inlining `(&&)` and performing beta substitution yields

```haskell
if expr1 == False then False else expr2
```

Performing beta substitution in PIR is typically incorrect, because in the `expr1 && expr2` example, before beta substitution, it evaluates `expr2` strictly, but afterwards, `expr2` is evaluated non-strictly.
But the latter is, in this instance, exactly what we want, which is why the INLINE pragma can be used to make an otherwise strict function non-strict.

This has recently been partially done by @michaelpj in [#5183](https://github.com/input-output-hk/plutus/pull/5183), which propagates `INLINE` pragmas but doesn't yet perform beta substitution.

Although non-strict functions can be defined this way, this approach is not a good way of defining arbitrary non-strict functions.
If we want a high level function `f` to be non-strict, we'd have to inline `f` and everything in the definition of `f`, all the way down to `if-then-else`!
This can easily explode script sizes.
Therefore, only a few simple functions like `(&&)` and `(||)` should be defined this way.

### Monomorphizing Plutus Tx Standard Library

Haskell's `Data.Foldable.any` function has the following type:

```haskell
any :: forall t. Foldable t => (a -> Bool) -> t a -> Bool
```

Because Haskell is a non-strict language, it is easy to define `any` in terms of `foldr`, which guarantees to short circuit:

```haskell
any p = foldr f False
  where f a acc = p a || acc
```

However, this definition of `any` does not work for Plutus Tx.
Recall the definition of `PlutusTx.foldr` for lists:

```haskell
foldr f z = go
  where
    go = \case
      []     -> z
      x : xs -> f x (go xs)
```

Because Plutus Tx is strict, `go xs` will be evaluated before evaluating `f`, which means `any` cannot short circuit. And since, like said before, Plutus Tx lacks a good way to define arbitrary non-strict functions, given this definition of `foldr`, there is no way to implement an `any` function with the above type, which guarantees to short-circuit for every `t` that has a `Foldable` instance.

We therefore choose to do the following for the Plutus Tx standard library:
- Provide the `Foldable` class and instances as they are, but make it clear that they cannot short-circuit.
- For functions that should short-circuit, such as `any` and `all`, we provide monomorphic versions of these functions (e.g., for lists), which are to be implemented without using `foldr`.

This is the same as what some other strict languages do in their stdlibs, such as Scala and OCaml.

It is worth mentioning that it is possible to implement a short-circuiting _and_ polymorphic `any`, if `Foldable` is defined in a different way, in which there are explicit suspensions and resumptions, e.g.,

```haskell
type Delay = (->) ()

delay :: a -> Delay a
delay a = \_ -> a

force :: Delay a -> a
force a = a ()

class Foldable_Delay t where
  foldr_delay :: (a -> Delay b -> Delay b) -> Delay b -> t a -> Delay b

instance Foldable_Delay [] where
  {-# INLINABLE foldr_delay #-}
  foldr_delay f z = go
    where
      go = \case
        [] -> z
        x : xs -> f x (delay (force (go xs)))

{-# INLINABLE any #-}
any :: Foldable_Delay t => (a -> Bool) -> t a -> Bool
any p = force . foldr_delay f (\_ -> False)
  where
    f a acc =
      if p a then delay True
      else acc
```

However, we will not be doing this in the standard library, because even though this version of `any` does short-circuit, it is not as efficient as the monomorphic version due to the additional cost from the `delay` and `force` machinery.
If this version is indeed preferred for some reason, it can be provided in a third party library.

### Turning off GHC's pre-inliner

As said before, one reason why the semantics of Plutus Tx is difficult to predict is because we run GHC's pre-inliner, which may perform unconditionally inlining.
Since GHC 9.0, GHC provides [an option](https://hackage.haskell.org/package/ghc-9.6.1/docs/GHC-Core-Opt-Simplify-Env.html#v:sm_pre_inline) to turn it off when running the simplifier.
By turning it off, GHC (hopefully) won't inline anything at all, which means it won't change the strictness of Plutus Tx programs.

At this time we can't simply turn the pre-inliner off, because doing so breaks the Plutus Tx compiler.
For details, see [this note](https://github.com/input-output-hk/plutus/blob/dc57fe1b8497835ef2a7794c017c5a50c0b7e647/plutus-tx-plugin/src/PlutusTx/Plugin.hs#L123).
The problem described in the note should, however, be resolved in a different way, as explained in the note.
Once done, we can go ahead and turn it off.

## Backwards Compatibility

Two of the proposed changes are non-backwards compatible in that they change the semantics of Plutus Tx: making let-bindings non-strict by default, and turning off GHC's pre-inliner.
We will add a plugin option to switch between the old and the new behaviors.
Initially the default will be the old behavior, and later the default will switch to be the new behavior.

## Decision

- We will update Plutus Tx documentation to encourage using `Strict` whenever appropriate.
- We will work on a solution that enables the Plutus Tx compiler to stop depending on GHC's pre-inliner.
- Once the above is done, we will introduce the `nonstrict` function which can be used to create non-strict let bindings in Plutus Tx.
- We will update the Plutus Tx standard library, by removing polymorphic functions that have more efficient monomorphic implementations (such as `PlutusTx.Foldable.any`), and providing monomorphic implementations instead.
