---
sidebar_position: 25
---

# Other Optimization Techniques

## Identifying problem areas

Profiling your script is a good way  to identify which parts of the script are responsible for significant resource consumption.
For more details, see [Profiling the Budget Usage of Plutus Scripts](../working-with-scripts/profiling-budget-usage.md).

## Using a Recent Version of the Plinth Compiler

The Plinth compiler is available through the `plutus-tx-plugin` package.
The Plutus team continuously improves compiler optimization, so using the latest or a recent version of `plutus-tx-plugin` will likely result in more compact and efficient scripts.

## Try `conservative-optimisation` or Flags Implied by It

Certain optimizations, such as inlining constants, can occasionally have negative effects, making scripts larger or more expensive.
It is worth disabling them to see how it affects your script.
You can do this using the `conservative-optimisation` plugin flag, which implies several other flags like `no-inline-constants`.
Alternatively, try turning on the flags implied by `conservative-optimisation` individually.
See [Plinth Compiler Options](../delve-deeper/plinth-compiler-options.md).

## Using the `Strict` Extension

The `Strict` extension, which makes all bindings in a module strict, generally improves performance.
See [GHC Extensions, Flags and Pragmas](../using-plinth/extensions-flags-pragmas.md) for an explanation.
However, care should be taken to avoid triggering unnecessary evaluations.
For example, in

```haskell
let a = <expr1>
    b = <expr2>
 in a && b
```

`b` will always be evaluated, even when `a` evaluates to `False`.
To avoid this, you can write either `~b = <expr2>`, or `a && <expr2>` (recall that `&&` and `||` are [special](../using-plinth/special-functions-and-types.md) in Plinth in that their second arguments are non-strict, unlike ordinary Plinth functions).
However, keep in mind that with `~b = <expr2>`, `<expr2>` will be evaluated each time `b` is referenced, since Plinth does not employ lazy evaluation, i.e., there is no memoization.

## Avoiding the `INLINE` Pragma

The `INLINE` pragma strongly encourages GHC to inline a function, even if it has a large body and is used multiple times.
This can lead to significant increase in the size of the resulting UPLC program, which is problematic since size is a much scarcer resource for Plutus scripts than for regular Haskell programs.

Instead, use the `INLINEABLE` pragma.
This would leave most inlining decisions to the PIR and UPLC inliners, which are tailored for Plutus scripts and make more informed inlining decisions.

## Be Mindful of Strict Applications

In Plinth, as with all strict languages, function applications are strict (call by value), with the exception of a few special functions like `&&` and `||`, which are treated specially by the compiler.

If you define your own version of `&&`:

```haskell
myAnd :: Bool -> Bool -> Bool
myAnd = (&&)
```

then it won't have the same behavior as `&&`, as it will always evaluate both arguments, even if the first argument evaluates to `False`.

It is particularly important to recognize that builtin functions like `chooseList` and `chooseData` are _not_ special, i.e., they are also strict in all arguments.
Thus the following example, which directly invokes the `chooseList` builtin, can be inefficient:

```haskell
res = PlutusTx.Builtins.Internal.chooseList xs nilCase consCase
```

It may even be semantically incorrect, if `nilCase = traceError "empty list"`, since it would always evaluate to an error.

Instead, use the wrapper provided by `PlutusTx.Builtins`, which suspends the evaluation of `nilCase` with a lambda:

```haskell
res = PlutusTx.Builtins.matchList (\_ -> nilCase) consCase
```

## Avoiding Intermediate Results

In a strict language, when composing several operations on a structure, the intermediate results are often fully materialized.
As examples, consider

```haskell
res1 = find (== 5) (xs ++ ys)
```

and

```haskell
res2 = sum (Map.elems m)
```

These are perfectly efficient in Haskell, but since function applications are strict in Plinth, the results of `xs ++ ys` and `Map.elems m` will be fully materialized before invoking `find` and `sum`, respectively.
You might consider rewriting these expressions to be less succinct but more efficient.

## Specializing higher-order functions

The use of higher-order functions is a common technique to facilitate code reuse.
Higher-order functions are widely used in the Plutus libraries but can be less efficient than specialized versions.

For instance, the Plutus function `findOwnInput` makes use of the higher-order function `find` to search for the current script input.

```haskell
findOwnInput :: ScriptContext -> Maybe TxInInfo
findOwnInput ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs},
             scriptContextPurpose=Spending txOutRef} =
    find (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == txOutRef) txInfoInputs
findOwnInput _ = Nothing
```

This can be rewritten with a recursive function specialized to the specific check in question.

``` haskell
findOwnInput :: ScriptContext -> Maybe TxInInfo
findOwnInput ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs},
             scriptContextPurpose=Spending txOutRef} = go txInfoInputs
    where
        go [] = Nothing
        go (i@TxInInfo{txInInfoOutRef} : rest) = if txInInfoOutRef == txOutRef
                                                 then Just i
                                                 else go rest
findOwnInput _ = Nothing
```

## Removing Traces

Traces can be expensive especially in terms of script sizes.
It is advisable to use traces during development, but to remove them when deploying your scripts on mainnet.
Traces can be removed via the `remove-trace` plugin flag.

## Using `BuiltinArray` for index-based lookups

For optimizing multiple index-based lookups, see the upcoming [Builtin Arrays](../upcoming-features/builtin-arrays.md) feature.


## Using `error` for faster failure

Plutus scripts have access to one impure effect, `error`, which immediately terminates the script evaluation and will fail validation.
This failure is very fast, but it is also unrecoverable, so only use it in cases where you want to fail the entire validation if there is a failure.

The Plutus libraries have some functions that fail with `error`.
Usually these are given an `unsafe` prefix to their name.
For example, `PlutusTx.IsData.Class.FromData` parses a value of type `Data`, returning the result in a `Maybe` value to indicate whether it succeeded or failed; whereas `PlutusTx.IsData.Class.UnsafeFromData` does the same but fails with `error`.
