---
sidebar_position: 5
---

# Plutus Tx compiler options

These options can be passed to the compiler via the `OPTIONS_GHC` pragma, for instance

``` haskell
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-uplc #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations=3 #-}
```

For each boolean option, you can add a `no-` prefix to switch it off, such as `no-typecheck`, `no-simplifier-beta`.

| Option                           | Value Type    | Default | Description |
|----------------------------------|---------------|---------|-------------|
| `conservative-optimisation`      | Bool          | False   | When conservative optimisation is used, only the optimisations that never make the program worse (in terms of cost or size) are employed. Implies `no-relaxed-float-in`.  |
| `context-level`                  | Int           | 1       | Set context level for error messages. |
| `coverage-all`                   | Bool          | False   | Add all available coverage annotations in the trace output |
| `coverage-boolean`               | Bool          | False   | Add boolean coverage annotations in the trace output |
| `coverage-location`              | Bool          | False   | Add location coverage annotations in the trace output |
| `defer-errors`                   | Bool          | False   | If a compilation error happens and this option is turned on, the compilation error is suppressed and the original Haskell expression is replaced with a runtime-error expression. |
| `dump-compilation-trace`         | Bool          | False   | Dump compilation trace for debugging |
| `dump-pir`                       | Bool          | False   | Dump Plutus IR |
| `dump-plc`                       | Bool          | False   | Dump Typed Plutus Core |
| `dump-uplc`                      | Bool          | False   | Dump Untyped Plutus Core |
| `max-cse-iterations`             | Int           | 4       | Set the max iterations for CSE |
| `max-simplifier-iterations-pir`  | Int           | 12      | Set the max iterations for the PIR simplifier |
| `max-simplifier-iterations-uplc` | Int           | 12      | Set the max iterations for the UPLC simplifier |
| `optimize`                       | Bool          | True    | Run optimization passes such as simplification and floating let-bindings. |
| `pedantic`                       | Bool          | False   | Run type checker after each compilation pass |
| `profile-all`                    | ProfileOpts   | None    | Set profiling options to All, which adds tracing when entering and exiting a term. |
| `relaxed-float-in`               | Bool          | True    | Use a more aggressive float-in pass, which often leads to reduced costs but may occasionally lead to slightly increased costs. |
| `remove-trace`                   | Bool          | False   | Eliminate calls to `trace` from Plutus Core |
| `simplifier-beta`                | Bool          | True    | Run a simplification pass that performs beta transformations |
| `simplifier-inline`              | Bool          | True    | Run a simplification pass that performs inlining |
| `simplifier-remove-dead-bindings`| Bool          | True    | Run a simplification pass that removes dead bindings |
| `simplifier-unwrap-cancel`       | Bool          | True    | Run a simplification pass that cancels unwrap/wrap pairs |
| `strictify-bindings`             | Bool          | True    | Run a simplification pass that makes bindings stricter |
| `target-version`                 | Version       | 1.1.0   | The target Plutus Core language version |
| `typecheck`                      | Bool          | True    | Perform type checking during compilation. |
| `verbosity`                      | Verbosity     | Quiet   | Set logging verbosity level (0=Quiet, 1=Verbose, 2=Debug) |


