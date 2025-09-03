---
sidebar_position: 80
---

# Troubleshooting

## Compilation Errors

### "No unfolding"

This means the plugin cannot access to the definition of a Haskell identifier, which it needs to be able to compile that identifier to Plutus Core.

If the identifier in question is defined in the source code, try adding the `INLINEABLE` pragma to it (not the `INLINE` pragma, which should generally be avoided).
If it already has the `INLINEABLE` pragma, try adding the GHC flags
`-fno-ignore-interface-pragmas` and `-fno-omit-interface-pragmas`.

If this doesn't resolve the issue, or if the identifier in question isn't directly defined in the code but is produced by GHC optimizations,
ensure that you apply all GHC flags listed in [GHC Extensions, Flags and Pragmas](./using-plinth/extensions-flags-pragmas.md).
These flags disable GHC optimizations that can interfere with the plugin, and ensure that unfoldings are neither omitted nor ignored.

If the identifier with missing unfolding is from `base` or invoked by a function from `base`, you should use instead the corresponding function from the `plutus-tx` package.
Note that the plugin lacks support for certain functions and methods from `base`.

This error can also occur if the definition of an identifier isn't available at compile time, as is the case with function parameters - e.g., `f x = $$(compile [|| x + 1 ||])`.
Here `x` is a parameter and thus has no unfolding at compile time.
To make this work, you should lift `x + 1` into `CompiledCode`, instead of compiling it.
See [Lifting Values into CompiledCode](./using-plinth/lifting.md) for more details.

Alternatively, this error may happen when using GHCi, which is not fully supported by the plugin.
Not only does GHCi often hide unfoldings from the plugin, but it may also introduce debugging information like breakpoints in GHC Core, causing the plugin to fail.

### "Unsupported feature: Cannot case on a value on type: \{type\}"

If `{type}` is a builtin type like `BuiltinInteger`: to convert a builtin type to the corresponding Haskell type (such as `BuiltinInteger` to `Integer` or `BuiltinList` to a Haskell list) in Plinth, you should use `fromOpaque`.
Pattern matching on the builtin type or using `fromBuiltin` is not permitted, and will lead to the above error.

If `{type}` is a GHC type like `GHC.Num.Integer.Integer`: you may be using operations from `base` (such as `GHC.Classes.==`) on that type, or using a literal of that type in a pattern.
An example of the latter:

```haskell
case (x :: Maybe Integer) of Just 42 -> ...
```

This is not supported, and you should instead write

```haskell
case (x :: Maybe Integer) of Just y | y PlutusTx.== 42 -> ...
```

### "Unsupported feature: Cannot construct a value of type"

Conversely, to convert a Haskell type to the corresponding builtin type in Plinth, you should use `toOpaque`, rather than directly using the data constructor or `toBuiltin`.

## Runtime Issues

### Missing Trace Messages

If your expected trace messages are missing, check the following [plugin flags](./delve-deeper/plinth-compiler-options.md):

- If the `remove-trace` flag (default off) is on, all trace messages will be removed.
- If the `preserve-logging` flag (default off) is off, the compiler may remove some trace messages during optimization.

### Unexpected Evaluation Failure

It is usually [advisable](./using-plinth/extensions-flags-pragmas.md) to use the `Strict` extension when writing Plinth, which improves performance.
However, be cautious, as this can result in unexpected evaluation failures.
Consider the following script:

```haskell
{-# LANGUAGE Strict #-}

data MyRedeemer = A | B

myScript :: MyRedeemer -> ScriptContext -> Bool
myScript redeemer ctx = case redeemer of
  A -> condition1
  B -> condition2
  where
    condition1, condition2 :: Bool
    condition1 = ...
    condition2 = if ... then True else traceError "condition 2 not met"
```

The `Strict` extension makes all bindings strict, which means even if `redeemer` matches `A`, `condition2` will still be evaluated.
This can be inefficient at best and, at worst, cause unexpected failures if `condition2` is not met when the redeemer matches `A`.

There are multiple ways to fix this:

1. You can make `condition1` and `condition2` non-strict by adding tildes:

```haskell
~condition1 = ...
~condition2 = ...
```

2. Alternatively, you can define `condition1` and `condition2` within the `case` branches:

```haskell
case redeemer of
  A -> let condition1 = ... in condition1
  B -> let condition2 = ... in condition2
```

3. Another option is to turn `condition1` and `condition2` into functions that take some arguments and return a `Bool`, as functions are not evaluated until all their arguments are provided.

## Haddock

The plugin will typically fail when producing Haddock documentation.
However, in this instance, you can simply tell it to defer any errors to runtime, using the `defer-errors` plugin flag. Since you are only building documentation, runtime errors won't occur.

## Error codes

Some Plinth library functions produce error messages when failing.
To reduce code size, error codes are used instead of full error messages.
The mapping from error codes to error messages can be found in [`PlutusTx.ErrorCodes`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/src/PlutusTx.ErrorCodes.html#plutusPreludeErrorCodes).
