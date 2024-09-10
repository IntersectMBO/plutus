---
sidebar_position: 80
---

# Troubleshooting

## Compilation Errors

### "No unfolding"

This means the plugin cannot access to the definition of a Haskell identifier, which it needs to be able to compile that identifier to Plutus Core.

If the identifier in question is defined in the source code, try adding the `INLINABLE` pragma to it (not the `INLINE` pragma, which should generally be avoided).
If it already has the `INLINABLE` pragma, try adding the GHC flags
`-fno-ignore-interface-pragmas` and `-fno-omit-interface-pragmas`.

If this doesn't resolve the issue, or if the identifier in question isn't directly defined in the code but is produced by GHC optimizations,
ensure that you apply all GHC flags listed in [Compiling Plutus Tx](./using-plutus-tx/compiling-plutus-tx.md).
These flags disable GHC optimizations that can interfere with the plugin, and ensure that unfoldings are neither omitted nor ignored.

If the identifier with missing unfolding is from `base` or invoked by a function from `base`, you should use instead the corresponding function from the `plutus-tx` package.
Note that the plugin lacks support for certain functions and methods from `base`.

This error can also occur if the identifier simply doesn't have an unfolding, e.g., `f x = $$(compile [|| x + 1 ||])`.
Clearly there is no unfolding for `x`, so it is impossible for it to work.

Last but not the least, this error may happen when using GHCi, which is not fully supported by the plugin.
Not only does GHCi often hides unfoldings from the plugin, but it may also introduce debugging information like breakpoints in GHC Core, causing the plugin to fail.

### "Unsupported feature: Cannot case on a value on type"

To convert a builtin type to the corresponding Haskell type (such as `BuiltinBool` to `Bool` or `BuiltinList` to a Haskell list) in Plutus Tx, you should use `fromOpaque`.
Pattern matching on the builtin type or using `fromBuiltin` is not permitted, and will lead to the above error.

### "Unsupported feature: Cannot construct a value of type"

Conversely, to convert a Haskell type to the correspoding builtin type in Plutus Tx, you should use `toOpaque`, rather than directly using the data constructor or `toBuiltin`.

## Runtime Issues

### Missing Trace Messages

If your expected trace messages are missing, check the following [plugin flags](./delve-deeper/plutus-tx-compiler-options.md):

- If the `remove-trace` flag (default off) is on, all trace messages will be removed.
- If the `preserve-logging` flag (default off) is off, the compiler may remove some trace messages during optimization.

## Haddock

The plugin will typically fail when producing Haddock documentation.
However, in this instance, you can simply tell it to defer any errors to runtime, using the `defer-errors` plugin flag. Since you are only building documentation, runtime errors won't occur.

## Error codes

Some Plutus Tx library functions produce error messages when failing.
To reduce code size, error codes are used instead of full error messages.
The mapping from error codes to error messages can be found in [`PlutusTx.ErrorCodes`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/src/PlutusTx.ErrorCodes.html#plutusPreludeErrorCodes).
