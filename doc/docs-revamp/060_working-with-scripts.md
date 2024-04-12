---
title: "Working with scripts"
description: "writing validator scripts, writing minting policies, creating and submitting transactions using an off-chain framework, libraries for writing Plutux Tx scripts, exporting scripts datums and redeemers, profiling the budget usage of Plutus scripts"
date: 2024-04-03
---

# Section 6. Working with scripts

- Writing basic validator scripts
   - Validator arguments
   - The Data type
   - Signaling failure
   - Validator functions
   - Plutus script context versions
- Writing basic minting policies
   - Minting policy arguments
   - Plutus script context versions
   - Writing minting policies
   - Other policy examples
- Creating and submitting transactions using an off-chain framework
- Libraries for writing Plutus Tx scripts
- Exporting scripts, datums and redeemers
- Profiling the budget usage of Plutus scripts
   - Compiling a script for profiling
   - Acquiring an executable script
   - Running the script
   - Analyzing the results

# Writing basic validator scripts

`Validator scripts<validator script>`{.interpreted-text role="term"} are the programs that can be used to lock transaction outputs on the chain.
Validator scripts are `Plutus Core`{.interpreted-text role="term"} programs, but we can use `Plutus Tx`{.interpreted-text role="term"} to write them easily in Haskell. 
Check out the `Plutus Tx tutorial<plutus_tx_tutorial>`{.interpreted-text role="ref"} before reading this one.

## Validator arguments

Validators receive some information from the validating node:

- The `redeemer`{.interpreted-text role="term"}, which is some script-specific data specified by the party spending the output.
- The `datum`{.interpreted-text role="term"}, which is some script-specific data specified by the party who created the output.
- The `script context`{.interpreted-text role="term"}, which contains a representation of the spending transaction, as well as the index of the input whose validator is currently being run.

The validator is a function which receives these three inputs as *arguments*. The validating node is responsible for passing them in and running the validator.

## The `Data` type

But how are the validator's arguments passed? 
Different scripts are going to expect different sorts of values in their datums and redeemers.

The answer is that we pass the arguments as a *generic* structured data type `PlutusCore.Data.Data`{.interpreted-text role="hsobj"}. 
`Data` is designed to make it easy to encode structured data into it, and is essentially a subset of CBOR.

Validator scripts take three arguments of type `Data`. 
Since `Data` is represented as a builtin type in Plutus Core, we use a special Haskell type `BuiltinData` rather than the underlying `Data` type.

However, you will typically not want to use `BuiltinData` directly in your program, rather you will want to use your own datatypes. 
We can easily convert to and from `BuiltinData` with the `PlutusTx.IsData.Class.ToData`{.interpreted-text role="hsobj"},
`PlutusTx.IsData.Class.FromData`{.interpreted-text role="hsobj"}, and `PlutusTx.IsData.Class.UnsafeFromData`{.interpreted-text role="hsobj"} typeclasses. 
You usually don't need to write your own instances of these classes. 
Instead, you can use the `unstableMakeIsData` or `makeIsDataIndexed` Template Haskell functions to generate one.

> **NOTE**
> 
> The `PlutusTx.IsData.Class.UnsafeFromData`{.interpreted-text role="hsobj"} class provides `unsafeFromBuiltinData`, which is the same as `fromBuiltinData`, but is faster and fails with `error` rather than returning a `Maybe`. 
> We'll use `unsafeFromBuiltinData` in this tutorial, but sometimes the other version is useful.

::: {.literalinclude start-after="BLOCK1" end-before="BLOCK2"}
BasicValidators.hs
:::

## Signaling failure

The most important thing that a validator can do is *fail*. 
This indicates that the attempt to spend the output is invalid and that transaction validation should fail. 
A validator succeeds if it does not explicitly fail. 
The actual value returned by the validator is irrelevant.

How does a validator fail? 
It does so by using the `PlutusTx.Builtins.error`{.interpreted-text role="hsobj"} builtin. 
Some other builtins may also trigger failure if they are used incorrectly (for example, `1/0`).

## Validator functions

We write validator scripts as Haskell functions, which we compile with Plutus Tx into Plutus Core. 
The type of a validator function is `BuiltinData -> BuiltinData -> BuiltinData -> ()`, that is, a function which takes three arguments of type `BuiltinData`, and returns a value of type `()` ("unit" or "the empty tuple" -- since the return type doesn't matter we just pick something trivial).

Here are two examples of simple validators that always succeed and always fail, respectively:

::: {.literalinclude start-after="BLOCK2" end-before="BLOCK3"}
BasicValidators.hs
:::

If we want to write a validator that uses types other than `BuiltinData`, we'll need to use the functions from `PlutusTx.IsData.Class.FromData`{.interpreted-text role="hsobj"} to decode them. 
Importantly, `unsafeFromBuiltinData` can fail: in our example, if the `BuiltinData` in the second argument is *not* a correctly encoded `Date`, then it will fail the whole validation with `error`, which is usually what we want if we have bad arguments.

> **Important**
> 
> Unfortunately, there's no way to provide failure diagnostics when a validator fails on chain -- it just fails. 
> However, since transaction validation is entirely deterministic, you'll always be informed of this before you submit the transaction to the chain, so you can debug it locally using `traceError`.

Here's an example that uses our date types to check whether the date which was provided is less than the stored limit in the datum.

::: {.literalinclude start-after="BLOCK3" end-before="BLOCK4"}
BasicValidators.hs
:::

## Plutus script context versions

Validators have access to the `script context`{.interpreted-text role="term"} as their third argument. 
Each version of Plutus validators are differentiated only by their `ScriptContext` argument.

> See this example from the file `MustSpendScriptOutput.hs` (lines 340 to 422) showing code addressing [Versioned Policies for both Plutus V1 and Plutus V2](https://github.com/IntersectMBO/plutus-apps/blob/05e394fb6188abbbe827ff8a51a24541a6386422/plutus-contract/test/Spec/TxConstraints/MustSpendScriptOutput.hs#L340-L422).

The script context gives validators a great deal of power, because it allows them to inspect other inputs and outputs of the current transaction. 
For example, here is a validator that will only accept the transaction if a particular payment is made as part of it.

::: {.literalinclude start-after="BLOCK4" end-before="BLOCK5"}
BasicValidators.hs
:::

This makes use of some useful functions for working with script contexts.

# Writing basic minting policies

`Minting policy scripts<minting policy script>`{.interpreted-text role="term"} are the programs that can be used to control the minting of new assets on the chain. 
Minting policy scripts are much like `validator scripts<validator script>`{.interpreted-text role="term"}, and they are written similarly, so check out the `basic validators tutorial<basic_validators_tutorial>`{.interpreted-text role="ref"} before reading this one.

## Minting policy arguments

Minting policies, like validators, receive some information from the validating node:

- The `redeemer`{.interpreted-text role="term"}, which is some script-specific data specified by the party performing the minting.
- The `script context`{.interpreted-text role="term"}, which contains a representation of the spending transaction, as well as the hash of the minting policy which is currently being run.

The minting policy is a function which receives these two inputs as *arguments*. The validating node is responsible for passing them in and running the minting policy. 
As with validator scripts, the arguments are passed encoded as `PlutusCore.Data.Data`{.interpreted-text role="hsobj"}.

## Plutus script context versions

Minting policies have access to the `script context`{.interpreted-text role="term"} as their second argument. 
Each version of Plutus minting policy scripts are differentiated only by their `ScriptContext` argument.

> See this example from the file `MustSpendScriptOutput.hs` (lines 340 to 422) showing code addressing [Versioned Policies for both Plutus V1 and Plutus V2](https://github.com/IntersectMBO/plutus-apps/blob/05e394fb6188abbbe827ff8a51a24541a6386422/plutus-contract/test/Spec/TxConstraints/MustSpendScriptOutput.hs#L340-L422).

Minting policies tend to be particularly interested in the `mint` field, since the point of a minting policy is to control which tokens are minted.

It is also important for a minting policy to look at the tokens in the `mint` field that use its own currency symbol i.e. policy hash. 
Note that checking only a specific token name is usually not correct. 
The minting policy must check for correct minting (or lack there of) of all token names under its currency symbol. 
This requires the policy to refer to its own hash --- fortunately this is provided for us in the script context of a minting policy.

## Writing minting policies

Here is an example that puts this together to make a simple policy that allows anyone to mint the token so long as they do it one token at a time. 
To begin with, we'll write a version that works with structured types.

::: {.literalinclude start-after="BLOCK1" end-before="BLOCK2"}
BasicPolicies.hs
:::

However, scripts are actually given their arguments as type `Data`, and must signal failure with `error`, so we need to wrap up our typed version to use it on-chain.

::: {.literalinclude start-after="BLOCK2" end-before="BLOCK3"}
BasicPolicies.hs
:::

## Other policy examples

Probably the simplest useful policy is one that requires a specific key to have signed the transaction in order to do any minting. 
This gives the key holder total control over the supply, but this is often sufficient for asset types where there is a centralized authority.

::: {.literalinclude start-after="BLOCK3" end-before="BLOCK4"}
BasicPolicies.hs
:::

> **Note**
> 
> We don't need to check that this transaction actually mints any of our asset type: the ledger rules ensure that the minting policy will only be run if some of that asset is being minted.

# Creating and submitting transactions using an off-chain framework

<!-- This used to be part of the Quick Start section. 
     The Quick Start section now points readers to the **plutus-tx-template** repo. 
     Factor in the content of: 
     https://github.com/IntersectMBO/plutus-tx-template
     -->

# Libraries for writing Plutus Tx scripts

This auction example shows a relatively low-level way of writing scripts using Plutus Tx.
In practice, you may consider using a higher-level library that abstracts away some of the details.
For example, [`plutus-apps`](https://github.com/IntersectMBO/plutus-apps) provides a constraint library for writing Plutus Tx.
Using these libraries, writing a validator in Plutus Tx becomes a matter of defining state transactions and the corresponding constraints. For example, the condition ``refundsPreviousHighestBid`` can simply be written as ``Constraints.mustPayToPubKey bidder (lovelaceValue amt)``.

# Exporting scripts, datums and redeemers

Since scripts must match their on-chain hashes exactly, it is important that the scripts which an application uses do not accidentally change.
For example, changing the source code or updating dependencies or tooling may lead to small changes in the script. 
As a result, the hash will change. 
In cases where the hashes must match exactly, even changes which do not alter the functionality of the script can be problematic.

For this reason, once you expect that you will not modify the on-chain part of your application more, it is sensible to *freeze* it by saving the final Plutus Core to a file.

Additionally, while most Plutus Applications use scripts by directly submitting them as part of transactions from the application itself, it can be useful to be able to export a serialized script. 
For example, you might want to submit it as part of a manually created transaction with the Cardano node CLI, or send it to another party for them to use.

Fortunately, it is quite simple to do this. 
Most of the types have typeclass instances for `Serialise` which allows translating directly into CBOR. 
This applies to `Validator`, `Redeemer`, and `Datum` types.
If you want to create values that you can pass to the Cardano CLI, you will need to convert them to the appropriate types from `cardano-api` and use `serialiseToTextEnvelope`.

::: {.literalinclude start-after="BLOCK5" end-before="BLOCK6"}
BasicValidators.hs
:::

`CompiledCode` has a different serialization method, `Flat`, but the principle is the same.

The serialized form of `CompiledCode` can also be dumped using a plugin option:

``` haskell
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-uplc #-}
```

This will dump the output to a temporary file with a name based on the module name. 
The filename will be printed to the console when compiling the source file. 
You can then move it to a more permanent location.

It can be read in conveniently with `loadFromFile` as an alternative to `compile`.

::: {.literalinclude start-after="BLOCK6" end-before="BLOCK7"}
BasicValidators.hs
:::

# Profiling the budget usage of Plutus scripts

Figuring out why your script takes more CPU or memory units than you expect can be tricky. 
You can find out more detail about how these resources are being used in your script by *profiling* it, and viewing the results in a flamegraph.

## Compiling a script for profiling

Profiling requires compiling your script differently so that it will emit information that we can use to analyse its performance.

> **Note**
> 
> As with profiling in other languages, this additional instrumentation can affect how your program is optimized, so its behaviour may not be identical to the non-profiled version.

To do this, you need to give a couple of options to the Plutus Tx plugin in the source file where your script is compiled.

``` haskell
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}
```

This instructs the plugin to insert profiling instrumentation for all functions. 
In the future there may be the option to profile a more targeted set of functions. 
It also makes sure that any inserted profiling instrumentation code would not be optimized away during PlutusTx compilation.

## Acquiring an executable script

Profiling works by seeing how the budget is used as the script runs. 
It therefore requires an executable script, which means that you need not only the validator script but all the arguments it receives. 
You can get this fully-applied script from the emulator or from the Cardano node.

## Running the script

You can run the script with the `uplc` executable.

> **Note**
> 
> All the executables referred to here can be built from the `plutus` repository using `cabal build`.

``` bash
uplc evaluate -i myscript.flat --if flat --trace-mode LogsWithBudgets -o logs
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
