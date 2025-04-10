---
sidebar_position: 23
---

# Compile Time Evaluation

Compile-time evaluation of expressions is usually preferable as it can reduce script size and execution cost.
There are several ways to achieve this.

## Relying on Compiler Optimizations

Some compiler optimizations - like constant folding and inlining - enable compile-time evaluation.
Constant folding reduces expressions such as `3 + 4` to `7`.
Inlining can result in beta-reduction - for example, `(\x -> x + y) 3` becomes `3 + y`.

Inlining can also unlock further optimizations; for instance, inlining `x` in `let x = 3 in x + 4` enables constant folding, eventually simplifying the expression to 7.
This requires `inline-constants` to be enabled (it is enabled by default).
Keep in mind that this may increase program size if a large constant appears multiple times.

This method is straightforward - you don't need to do anything manually; the compiler handles it for you.
The catch is that you’re limited to what the compiler is able (and willing) to optimize.

Specifically, at present constant folding is limited to builtin functions applied to constant arguments.
It won't, for example, reduce `x * 0` to `0`, or `3 + (4 + x)` to `7 + x`.
Inlining happens only when the compiler knows it is safe (i.e., won’t alter the program semantics) and beneficial (i.e., won’t substantially increase program size or cost).
The compiler is conservative in both respects, though the inliner can be made more aggressive using the `inline-callsite-growth` flag.

## Using Template Haskell

This is a standard Haskell metaprogramming technique for evaluating and generating code at compile time.
Since Plinth is a subset of Haskell, it applies equally to Plinth.

Template Haskell offers a lot of power, but it also introduces a fair bit of complexity, syntactic overhead and cognitive burden.
It lets you generate arbitrary Haskell code at compile time, so you can do everything from basic constant folding to far more advanced transformations - see [Simplifying Code Before Compilation](./simplifying-before-compilation.md) for more examples.
A general principle is to reserve this for cases where the complexity of the problem really calls for it.

Even putting the complexity aside, this method may still be unsuitable depending on what transformation you want to apply.
For example, to implement a general constant folding optimizer for `addInteger`, you may need to handle all possible syntaxes for adding two integers: `addInteger 3 4`, `3 + 4`, and even ``3 `addInteger` 4``.
This is why optimizations like constant folding are better done in a smaller intermediate language, rather than in the surface language.
And if you also want to perform inlining - such as rewriting `let x = 3 in addInteger x 4` to `7`, then it's even more difficult.

For simple compile-time evaluation like constant folding, it is better  to let the compiler handle it.
Use Template Haskell for complex transformations, or transformations that the Plinth compiler can't yet do.

## Using Lifting

You can find a detailed explanation of lifting in [Lifting Values into CompiledCode](../using-plinth/lifting.md).
Lifting is a regular Haskell function application that happens at runtime, and it always operates on values that have been fully evaluated.
For instance, when you call `liftCodeDef (...)` where the argument - `(...)` - is some complex Haskell computation of type `Integer`, `liftCodeDef` will evaluate the argument to an integer constant, and produce a `CompiledCode` that contains a PIR/UPLC constant.

It is important to understand that the "runtime" here is the _runtime of your Haskell program_, __not__ the runtime (on-chain execution) of your script.
So from the script's perspective, this is still compile-time evaluation, as it is still part of the process of creating the script to be executed on-chain.

The fact that lifting happens at runtime, rather than compile time, of your Haskell program, gives it some unique advantages:

- This is the only way to turn values that are only known at runtime into `CompiledCode`.
- The value being lifted can come from any arbitrary Haskell computation.
  You can, for example, write arbitrary Haskell code that produces an `Integer`, and lift it into `CompiledCode`.
  This code can read from a file, or do anything else possible in Haskell.

The main limitation is that, in general, functions, or any data type containing functions, cannot be lifted.
Indeed, given a Haskell function at runtime, you can only call it with some arguments - you cannot inspect it or reify it into a `CompiledCode`.
