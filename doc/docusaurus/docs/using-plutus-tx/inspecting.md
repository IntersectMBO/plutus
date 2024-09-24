---
sidebar_position: 30
---

# Inspecting Compilation and Compiled Code

On this page, you’ll learn how to look into the compilation of Plutus Tx and the resulting compiled code, which you might want to do for reasons such as debugging and tuning.

## Inspecting the Compilation

In the event of a compilation failure, a trace of compilation steps leading to the problematic GHC Core expression is printed.
This is comparable to the stack trace from a program encountering an uncaught exception.
For example, if you use an unsupported Haskell feature, causing the compilation to fail, this trace can often help you identify where it appears in the source code.

Another way of inspecting the compilation is by using the `dump-compilation-trace` plugin flag:

```haskell
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-compilation-trace #-}
```

This compilation trace has two main differences from the previously mentioned trace:

- It prints every single step taken by the compiler, as the compilation proceeds, rather than just the trace leading to the failure.
- It can be used to show the trace whether the compilation succeeded or failed.
  This is convenient because sometimes you might want to compare the trace of a failed compilation against the trace of a succeeded compilation to figure out where it went wrong.

In the compilation trace, to make it easier to figure out how the compilation got to a certain point, every step is annotated with an ID along with the ID of the parent step.

## Inspecting the Compiled Code

A `CompiledCode` obtained through normal compilation includes a UPLC program along with the corresponding PIR program.
PIR is an intermediate representation used by the Plutus Tx compiler.
It is much more readable than UPLC, so for tasks such as debugging and performance tuning, it is usually more helpful to insepct PIR, but there are also instances where looking into UPLC directly is necessary.

The PIR and UPLC programs can be retrieved from the `CompiledCode` via `getPirNoAnn` and `getPlcNoAnn` from [`PlutusTx.Code`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Code.html).
The annotations are usually not needed, but if you do need them, use `getPir` and `getPlc` instead.

The `plutus-core` library provides several ways for pretty-printing PIR and UPLC programs.
There are two main configuration options for pretty-printing:
- Choosing between the classic syntax or a more readable syntax.
- Choosing whether to show uniques.
  Uniques are numerical identifiers assigned to variable names; while they ensure unambiguity, they can introduce clutter.

The following table shows the functions for pretty-printing PIR and UPLC programs.
All these are from the [`PlutusCore.Pretty`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-core/PlutusCore-Pretty.html) module.

| |Classic Syntax|Readable Syntax|
|-|-|-|
|No Uniques|`prettyClassicSimple`|`prettyReadableSimple`|
|With Uniques|`prettyClassic`|`prettyReadable`|
