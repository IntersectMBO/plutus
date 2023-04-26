# ADR 5: Plutus Tx's Evaluation Strategy, Compiler and Standard Library

Date: 2023-04

## Authors

Ziyang Liu <ziyang.liu@iohk.io>

## Status

Proposed

## Background

Plutus Tx is a language for writing Plutus scripts.
It is a subset of Haskell and can be compiled to Untyped Plutus Core (hereafter referred to as PLC) by the Plutus Tx compiler, a GHC plugin.

Haskell uses lazy evaluation (call by need) by default, while PLC is strict (call by value).
This begs the question: what is the operational semantics of Plutus Tx?
This is an important question, the answer of which not only dictates how users of Plutus Tx should reason about and optimize their programs, but also has major implications on the design and implementation of the Plutus Tx compiler and libraries.

Unfortunately, this question is currently difficult to answer.
One thing is clear: Plutus Tx certainly doesn't have lazy semantics: PLC's evaluator (the CEK machine) has no support for thunks and memoization.
What is unclear is whether Plutus Tx is strict or non-strict.
Indeed, it is sometimes strict and sometimes non-strict, and it is fairly random and difficult to predict:

- Let-bindings in Plutus Tx are by default non-strict, but function applications are strict.
  That is, `let x = rhs in body` isn't equivalent to `(\x -> body) rhs`.
  This is distinct from most other languages, regardless of their evaluation strategies, in which these two expressions are equivalent.

- The conditional expression `if b then t else f` is always non-strict in `t` and `f`, like in most strict languages.
  But what about `foo b t f = if b then t else f`? In a strict language, `foo` would be strict, and in a non-strict language, it would be non-strict.
  But in Plutus Tx, due to how its compiler is currently implemented, whether `t` and `f` are evaluated strictly or not depends on whether GHC inlines `foo`.
  Although we turn off GHC's inliner in the Plutus Tx compiler, GHC may still decide to unconditionally inline `foo` if it is used only once.
  In general, it is not easy to predict whether GHC will inline something or not.

The lack of consistency makes it difficult to reason about the efficiency of Plutus Tx programs, and difficult to write useful libraries for Plutus Tx that guarantee to have the desirable behaviors (e.g., short-circuiting).

This ADR proposes a few changes to the Plutus Tx language and the compiler to make the semantics more predictable.
It also proposes changes to the Plutus Tx standard library to make it more performant.

## Proposed Changes

Plutus Tx should be a strict-by-default language.
Non-strict-by-default languages are rarely used in practice since non-strict evaluation leads to repeated evaluations.
Unless we implement lazy evaluation for PLC in the future, strictness should be the default for Plutus Tx.
Given this, the following changes are proposed.

### Making Let-bindings Strict By Default

In a strict-by-default language, it would make sense that let-bindings be strict by default, since that's what almost all strict languages do; plus, non-strict bindings should be used cautiously since they can easily lead to unbounded amount of repeated evaluation.
But if make let-bindings strict by default, then the question is, how does one make a non-strict let-binding?

Haskell supports lazy patterns with the `~` operator, and it can be used on let-bindings, e.g., `let ~x = rhs`. So one possibility is to make non-strict let-bindings this way.
However, lazy pattern has no effect on simple pattern bindings (i.e., the pattern is a single variable), and it makes no difference in GHC Core, which means the Plutus Tx compiler can't actually see the `~`.
It is technically possible to make `~` work but it would require adding a GHC parser plugin to capture `~` in GHC Core, among other things, adding a great deal of complexity.

This is the reason why let-bindings have been non-strict by default in Plutus Tx, and creating strict let-bindings requires using bang patterns.

However, we can do it in a different way.
Although we can't modify Haskell's syntax, we can introduce functions to be handled specially by the Plutus Tx compiler.
Specifically, we can introduce the following function:

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

What if `x` gets inlined by GHC, i.e., GHC turns `let x = nonstrict rhs in ...x...` into `...(nonstrict rhs)...`?
That's not a problem, although it needs to be dealt with in a different way.
If we see a `nonstrict rhs` that isn't the RHS of a binding, we first compile `rhs` normally.
Then, we annotate `compiled_rhs` with `NONSTRICT`.
The effect of `NONSTRICT` is: when the beta-reduction pass creates let-bindings from arguments, it normally creates strict bindings; but if an argument is annotated with `NONSTRICT`, then it creates a non-strict binding instead.

By doing so, the `nonstrict` function can be used not only to create non-strict bindings, but also make a function evaluate an argument non-strictly, making it an handy tool for writing Plutus Tx code, especially library code.
See the next section.

### Using `nonstrict` to Make Arguments Non-strict

Consider the definition of `PlutusTx.foldr` for lists:

```haskell
foldr f z = go
  where
    go = \case
      []     -> z
      x : xs -> f x (go xs)
```

Since Plutus Tx is strict by default, this `foldr` definition cannot short-circuit, because `go xs` will be evaluated before evaluating `f`.
It is not sufficient to create a non-strict binding for `go xs` (i.e., `let y = go xs in f x y`) because GHC will unconditionally inline `y`.

The problem can be solved by using `nonstrict`, replacing `f x (go xs)` with `f x (nonstrict (go xs))`.
Now `go xs` is evaluated non-strictly, and `foldr` can short-circuit.
However, this can lead to less efficient code, if the second argument of `f` is used more than once.
For that reason, it may be a good idea to provide both a strict version and a non-strict version of `foldr`.

Some strict languages have special syntaxes to mark a function lazy in a particular argument, e.g., Scala has the `=>` syntax.
The following function is strict in the first argument and lazy in the second argument:

```scala
def foo(a: Int, b: => Int) { ... }
```

`nonstrict` can be used to achieve a similar effect, except that `nonstrict` is used at the call sites as opposed to function definitions.

#### `foldr` and `nonstrict` in Other Strict Languages

Scala and OCaml are both strict by default.
In both languages, their version of `foldr` for lists in the respective standard library ([Scala](https://www.scala-lang.org/api/2.13.3/scala/collection/immutable/List.html#foldRight[B](z:B)(op:(A,B)=%3EB):B),[OCaml](https://v2.ocaml.org/api/List.html)) is strict and doesn't short circuit.
Functions that should short-circuit, such as `all` and `any`, do short-circuit, and unsurprisingly they are not implemented in terms of `foldr`.

Scala's [cats library](https://github.com/typelevel/cats) provides a `Foldable` typeclass, and a short-circuiting `foldRight`.
In order to do so, cats' `foldRight` has a different type than the one in the standard library: the type of the accumulator is `Eval b` rather than `b`.
Our `nonstrict` function is similar to `Eval.always`, except that `nonstrict`'s type is `a -> a` while the type of `Eval.always` is `a -> Eval a` - because it is a library, not a plugin.
Incidentally, there's a simpler way to make `foldRight` lazy using Scala's built-in syntax for lazy arguments, but it is not stack safe.
Interestingly, the `Foldable.forall` and `Foldable.exists` functions in cats are implemented by [converting the foldable structure to list first](https://github.com/typelevel/cats/blob/896f00cd689af20676556d1b57791d7ade5cfa04/core/src/main/scala/cats/Foldable.scala#L677-L686), rather than using `foldRight`.

We can potentially introduce something similar to `Eval` in the Plutus Tx standard library.
The advantage of `Eval` is that it can be provided entirely in a library, without special compiler support. However, this is also what leads to its disadvantage: `Eval` is more heavyweight to use, since it changes the types of many functions (such as `foldr`), while `nonstrict` has the same type as the identity function, which is possible because it is a magical function that the compiler treats specially.

The takeaway is this: the standard libraries usually do the simple things, e.g., providing a monomorphic, non-short-circuiting version of `foldr` for lists, as well as functions like `all`, `any`, also monomorphically for lists.
The polymorphic versions of those functions, if exist, are usually provided by third-party libraries like cats.

### Define non-strict functions

In Plutus Tx, like most other strict languages, only a few built-in constructs are non-strict (such as if-then-else).
It is cumbersome, if not impossible, to create user-defined non-strict functions.
The `nonstrict` function described before does not help because it cannot be used in defining a function.
It would be useful to allow user-defined non-strict functions, so that we can define functions like `&&` and `||` that short-circuit properly.
Some languages like Scala have special syntaxes for defining non-strict functions; we can't change Haskell's syntax, so we need to find a different solution.

The idea is to make the Plutus Tx compiler perform GHC-like inlining for functions with the INLINE pragma.

"GHC-like inlining", or "inlining in the GHC way", for lack of a better term, refers to inlining in a way similar to how GHC does it, i.e., replacing a variable with its RHS, then performing beta substitution.
As an example, consider the definition of `(&&)`:

```haskell
(&&) :: Bool -> Bool -> Bool
a && b = if a == False then False else b
{-# INLINE && #-}
```

When the PIR inliner inlines `(&&)` in the normal way, `expr1 && expr2` becomes

```haskell
let !x = expr1
    !y = expr2
 in if x == False then False else y
```

whereas inlining `(&&)` in the GHC way yields

```haskell
if expr1 == False then False else expr2
```

Normally, it is incorrect for the Plutus Tx compiler to inline `(&&)` in the GHC way, because in the `expr1 && expr2` example, before inlining, it evaluates `expr2` strictly, but after GHC-like inlining, `expr2` is evaluated non-strictly.
But because of the `INLINE` pragma, the Plutus Tx compiler should inline `(&&)` in the GHC way.
And this is desirable because we want `(&&)` to be non-strict.
Functions that should not be inlined in the GHC way should use the `INLINABLE` pragma.

This has recently been partially done by @michaelpj [#5183](https://github.com/input-output-hk/plutus/pull/5183), which propagates `INLINE` pragmas but doesn't yet perform GHC-like inlining.

### Monomorphizing Plutus Tx Standard Library

For Plutus Tx, even with the ability to define non-strict bindings and functions, it is still useful to provide monomorphic versions of certain functions in the standard library, especially since they can be noticeably cheaper than the polymorphic versions.

Strict languages do not lend themselves to code reuse, as there is a high cost to use abstractions such as higher-order functions and ad-hoc polymorphism.
Polymorphic functions taking `Foldable` or similar constraints, implemented in terms of higher-order functions like `foldr`, are rare in strict languages.

For Plutus Tx, there's another reason why monomorphization of the standard library is beneficial: multiple method typeclasses are expensive.

Single method typeclasses are cheap because they have simpler representations in GHC Core - a newtype that can be compiled away.
On the other hand, multiple method typeclasses exist in GHC Core as actual dictionaries and need to be compiled into product types in PIR.

This makes monomorphization the only choice in many cases. Consider `foldr` and `foldMap`.
They can be implemented in terms of each other, so technically, only one of them needs to be in the `Foldable` class.
But certain types have more efficient direct implementations of `foldr`; the same for `foldMap`.
No matter which of them we move out of `Foldable`, it won't work optimally for certain types.
Keeping both in `Foldable` will cause `Foldable` to be a multiple method typeclass, which is expensive in and of itself, as explained above.
We may as well do away with `PlutusTx.Foldable`, and instead simply provide monomorphic versions of `Foldable`-related functions for each common type.

### Turning off GHC's pre-inliner

As said before, one reason why the semantics of Plutus Tx is difficult to predict is because we run GHC's pre-inliner, which may perform unconditionally inlining.
Since GHC 9.0, GHC provides [an option](https://hackage.haskell.org/package/ghc-9.6.1/docs/GHC-Core-Opt-Simplify-Env.html#v:sm_pre_inline) to turn it off when running the simplifier.
By turning it off, GHC (hopefully) won't inline anything at all, which means it won't change the strictness of Plutus Tx programs.

At this time we can't simply turn the pre-inliner off, because doing so breaks the Plutus Tx compiler.
For details, see [this note](https://github.com/input-output-hk/plutus/blob/dc57fe1b8497835ef2a7794c017c5a50c0b7e647/plutus-tx-plugin/src/PlutusTx/Plugin.hs#L123).
The problem described in the note should, however, be resolved in a different way, as explained in the note.
Once done, we can go ahead and turn it off.
