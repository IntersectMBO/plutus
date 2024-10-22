---
sidebar_position: 30
---

# Profiling Script Budget Usage

Figuring out why your script takes more CPU or memory units than you expect can be tricky.
You can find out more detail about how these resources are being used in your script by profiling it, and viewing the results in a flamegraph.

## Compiling a script for profiling

Profiling requires compiling your script differently so that it will emit information that we can use to analyse its performance.

> :pushpin: **NOTE**
>
> As with profiling in other languages, this additional instrumentation can affect how your program is optimized, so its behavior may not be identical to the non-profiled version.

To do this, use the `profile-all` and `conservative-optimisation` plugin flags:

``` haskell
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}
```

This instructs the plugin to insert profiling instrumentation for all functions.
In the future there may be the option to profile a more targeted set of functions.
The `conservative-optimisation` flag makes sure that any inserted profiling instrumentation code would not be optimized away during PlutusTx compilation.

## Running the script

You can run a script using the `uplc` executable, which can be downloaded from each [Plutus release](https://github.com/IntersectMBO/plutus/releases).
If no pre-built executable is available for your architecture, you can build it from source using `cabal build uplc`.

Keep in mind that the budget is consumed as the script runs, so you need both the script and all its arguments, and create a fully applied script by applying the script to all arguments.

Given a script and its arguments, a fully applied script can be obtained via

```bash
uplc apply script arg1 arg2 ... argn
```

Once you have the fully applied script, you can evaluate it using the `uplc` executable, with a command like the one below:

```bash
uplc evaluate -i fully-applied-script.flat --if flat --trace-mode LogsWithBudgets -o logs
```

This runs the script using the trace mode that emits budget information, and puts the resulting logs in a file.
This will be a CSV file with three columns: a message indicating which function we are entering or exiting; the cumulative CPU used at that time; and the cumulative memory used at that time.

## Analyzing the results

We can then convert the logs into a flamegraph using the standard `flamegraph.pl` tool.
The `traceToStacks` executable turns the logs into a format that `flamegraph.pl` understands

``` bash
cat logs | traceToStacks | flamegraph.pl > cpu.svg
cat logs | traceToStacks --column 2 | flamegraph.pl > mem.svg
```

Since `flamegraph.pl` can only handle one metric at a time, `traceToStacks` has a `--column` argument to select the other column if you want to get a memory flamegraph.

You can then view the resulting SVGs in a viewer of your choice, such as a web browser.

Alternatively, there are other, more powerful, tools that understand the format produced by `traceToStacks`, such as [speedscope](https://www.speedscope.app/).
