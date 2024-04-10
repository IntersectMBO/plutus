---
title: "Reference"
description: "TBD"
date: 2024-04-10
---

# Section 8. Reference

- Writing scripts
   - Plutus Tx compiler options
   - Optimization techniques for Plutus scripts
      - Identifying problem areas
      - Using strict let-bindings to avoid recomputation
      - Specializing higher-order functions
      - Common sub-expression elimination
      - Using `error` for faster failure
   - Common weaknesses
      - Double satisfaction
      - Hard limits
- Plutus on Cardano
   - Plutus language changes
   - Upgrading to Vasil and Plutus script addresses
   - Cost model parameters
- Glossary
- Bibliography

-------

# Writing scripts

## Plutus Tx Compiler Options

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


## Optimization techniques for Plutus scripts

### Identifying problem areas

<!-- The link in this paragraph needs to become a cross-reference -->

In order to identify which parts of the script are responsible for significant resource consumption, you can use the `profiling support <profiling_scripts>`{.interpreted-text role="ref"}.

### Using strict let-bindings to avoid recomputation

Let-bindings in Haskell are translated to strict let-bindings in Plutus IR, unless they look like they might do computation, in which case they are translated to non-strict let-bindings. 
This is to avoid triggering effects (e.g. errors) at unexpected times.

However, non-strict let-bindings are less efficient. 
They do not evaluate their right-hand side immediately, instead they do so where the variable is used. 
But they are not *lazy* (evaluating the right-hand side at most once), instead it may be evaluated once each time it is used. 
You may wish to explicitly mark let-bindings as strict in Haskell to avoid this.

``` haskell
-- This may be compiled non-strictly, which could result
-- in it being evaluated multiple times. However, it will
-- not be evaluated if we take the branch where it is not used.
let x = y + z
in if b then x + x else 1

-- This will be compiled strictly, but this will mean it
-- is evaluated even if we take the branch where it is not used.
let !x = y + z
in if b then x + x else 1
```

### Specializing higher-order functions

The use of higher-order functions is a common technique to facilitate code reuse.
Higher-order functions are widely used in the Plutus libraries but can be less efficient than specialized versions.

For instance, the Plutus function `findOwnInput` makes use of the higher-order function `find` to search for the current script input.

``` haskell
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

### Common sub-expression elimination

When several instances of identical expressions exist within a function's body, it's worth replacing them with a single (strict) let-bound variable to hold the computed value.

In this example, the cost of storing and retrieving `n * c` in a single variable is significantly less than recomputing it several times.

``` haskell
let a' = a `divide` n * c
    -- occurrence 1
    b' = b * (n * c)
    -- occurrence 2
    C' = c + (n * c)
in
  foo a' b' c' n

-- Only one occurrence
let !t_mul = n * c
    a' = a `divide` t_mul
    b' = b * t_mul
    c' = c + t_mul
in
  foo a' b' c' n
```

### Using `error` for faster failure

Plutus scripts have access to one impure effect, `error`, which immediately terminates the script evaluation and will fail validation.
This failure is very fast, but it is also unrecoverable, so only use it in cases where you want to fail the entire validation if there is a failure.

The Plutus libraries have some functions that fail with `error`. 
Usually these are given an `unsafe` prefix to their name. 
For example, `PlutusTx.IsData.Class.FromData`{.interpreted-text role="hsobj"} parses a value of type `Data`, returning the result in a `Maybe` value to indicate whether it succeeded or failed; whereas `PlutusTx.IsData.Class.UnsafeFromData`{.interpreted-text role="hsobj"} does the same but fails with `error`.

## Examples

Full examples of Plutus Applications can be found in the `plutus-apps` [repository](https://github.com/IntersectMBO/plutus-apps/tree/master/plutus-use-cases).
The source code can be found in the `src` and the tests in the `test` folder.

The examples are a mixture of simple examples and more complex ones, including:

- A crowdfunding application
- A futures application
- A stablecoin
- A uniswap clone

> **Important**
>
> Make sure to look at the same version of the [plutus-apps]{.title-ref} repository as you are using, to ensure that the examples work.

## Common weaknesses

This section provides a listing of common *weaknesses* in Plutus applications. "Weakness" is used in the sense of the [Common Weakness Enumeration](https://cwe.mitre.org/), as a potential source of vulnerabilities in applications.

### Double satisfaction

Suppose we have a validator V that implements a typical "atomic swap" or "escrowed swap" between A and B where A goes first, i.e. V says:

> This output can only be spent if, in the same transaction, there is an output sending the agreed-upon payment (encoded in the output's datum) to A.

Now suppose that A and B have two swaps in progress, one for a token T1 at the price of 10 Ada, and one for a token T2 at the same price. 
That means that there will exist two outputs, both locked by V.

Now B constructs a transaction which spends both outputs, and creates one output addressed to A with 10 Ada (taking T1 and T2 for himself).

<figure>
<img src="double-satisfaction.png" alt="double-satisfaction.png" />
<figcaption>A diagram showing the transaction setup for the double satisfaction of two swaps.</figcaption>
</figure>

A naive implementation of V will just check that the transaction has *an* output to A with 10 Ada in it, and then be satisfied. 
But this allows B to "double satisfy" the two validators, because they will both see the same output and be satisfied. 
The end result is that B can get away with paying only 10 Ada to A, even though B's true liability to A is 20 Ada.

**What is going wrong here?**

It is difficult to say exactly what is going wrong here. 
Neither validator's expectations are explicitly being violated.

One way of looking at it is that this is a consequence of the fact that validators only *validate*, rather than *doing* things. 
In a model like Ethereum's, where smart contracts *make transfers*, then two smart contracts would simply make two transfers, and there would be no problem. 
But in the EUTXO model all a validator can do is try to ascertain whether its wishes have been carried out, which in this case is ambiguous.

Following this metaphor, we can see how the same problem could arise in the real world. 
Suppose that two tax auditors from two different departments come to visit you in turn to see if you've paid your taxes.
You come up with a clever scheme to confuse them. 
Your tax liability to both departments is $10, so you make a single payment to the tax office's bank account for $10. 
When the auditors arrive, you show them your books, containing the payment to the tax office. 
They both leave satisfied.

How do we solve this problem in the real world? 
Well, the two tax offices might have different bank accounts, but more likely they would simply require you to use two different payment references. 
That way, the payment that each auditor expect to see is unique, so they know it's for them. 
We can do something similar in the EUTXO model. 
See the section on [Unique outputs](#unique-outputs) below.

**Risks**

This is a serious problem for many kinds of application. 
Any application that makes payments to specific parties needs to ensure that those payments are correctly identified and don't overlap with other payments.

**Solutions**

It's possible that a solution will be developed that makes this weakness easier to avoid. 
In the mean time, there are workarounds that developers can use.

- **Unique outputs**

The simplest workaround is to ensure that the outputs which your scripts care about are unique. 
This prevents them being confused with other outputs.

In the swap example, if A had used a different key hashes as their payment addresses in each, then one output could not have satisfied both validators, since each one would want an output addressed to a different key hash.

It is not too difficult to use unique outputs. 
For payments to users, wallets typically already generate unique key hashes for every payment received. 
For payments to script addresses it is a bit more complicated, and applications may wish to include the equivalent of a "payment reference" in the datum to keep things unique.

- **Ban other scripts**

A more draconian workaround is for your script to insist that it runs in a transaction which is running no other scripts, so there is no risk of confusion. 
Note that it is not enough to consider just validator scripts, minting and reward scripts must also be banned.

However, this prevents even benign usage of multiple scripts in one transaction, which stops people from designing interesting interactions, and may force users to break up transactions unnecessarily.

### Hard limits

Many resources on Cardano are limited in some fashion. 
At a high level, limits can be enforced in two ways:

- *Hard limits*: these are limits which cannot be breached. Typically, these are implemented with specific thresholds, where exceeding the threshold causes a hard failure.
- *Soft limits*: these are limits which *can* be breached, but where there is a significant disincentive to do so. One way of implementing a soft limit is to have sharply increasing costs to using the resource beyond the soft limit.

Hard limits are clear, easy to specify, and provide hard guarantees for the protocol, but they have the disadvantage that there is no way to evade the limit. 
This means that there is a discontinuity at the limit: beforehand you can always do more by paying more, but after the limit there is nothing you can do.

Currently, these resources on Cardano have hard limits:

- Transaction size
- Block size
- UTXO size
- Script execution units

If an application *requires* a transaction that exceeds one of these limits, then the application will be stuck unless the limit is increased or removed. 
This is most common when scripts are involved, since a script can require a very particular shape of transaction, regardless of whether this exceeds limits.

Examples:

- A script requires providing a datum which is extremely large and exceeds the transaction size limit.
- A script which locks an output needs more execution units than the limit.
- A script requires creating a single output containing a very large amount of tokens, which exceeds the output size limit.

**Risks**

This is typically an issue for applications that work with user-supplied data, or data that can grow in an unbounded way over time. 
This can result in data which itself becomes large, or which requires a large amount of resources to process.

For example:

- Managing an arbitrary collection of assets (unbounded over time).
- Allowing user-specified payloads in datums (user-supplied unbounded data).

Script size should not itself be a risk (since scripts and their sizes should generally be known ahead of time), but large scripts can reduce the amount of space available for other uses, heightening the risk of hitting a limit.

**Solutions**

In the long run, hard limits may be increased, removed, or turned into soft limits.

In the mean time, there are some approaches that developers can use to reduce the risk.

- **Careful testing**

It is important to test as many of the execution paths of your application as possible. 
This is important for correctness, but also to ensure that there are not unexpected cases where script resource usage spikes.

- **Bounding data usage**

Carefully consider whether your application may rely on unbounded data, and try to avoid that. 
For example, if your application needs to manage a large quantity of assets, try to split them across multiple UTXOs instead of relying on a single UTXO to hold them all.

- **Providing datums when creating outputs**

Datum size issues are most likely to be discovered when an output is spent, because the datum is provided only as a hash on the output.
Insisting that the datum is provided in the transaction that creates the output can reveal that it is too big earlier in the process, allowing another path to be taken. 
Depending on the application, this may still prevent it from progressing, if there is only one way to move forwards.

If [CIP-32](https://cips.cardano.org/cips/cip32/) is implemented, this can be done conveniently by using inline datums, although that also risks hitting the output size limit.

- **Reducing script size costs through reference inputs**

If [CIP-33](https://cips.cardano.org/cips/cip33/) is implemented, then the contribution of scripts to transaction size can be massively reduced by using a reference script instead of including the entire script.

<!-- Verify that CIP-32 and CIP-33 have already been implemented, and update statements above as appropriate. -->

# Plutus on Cardano

## Plutus language changes

### Language versions

See the documentation on `language versions <what_are_plutus_language_versions>`{.interpreted-text role="ref"} for an explanation of what they are.

#### Plutus V1

`PlutusV1` was the initial version of Plutus, introduced in the Alonzo hard fork.

#### Plutus V2

`PlutusV2` was introduced in the Vasil hard fork.

The main changes in `PlutusV2` were to the interface to scripts. 
The `ScriptContext` was extended to include the following information:

- The full "redeemers" structure, which contains all the redeemers used in the transaction
- Reference inputs in the transaction (proposed in [CIP-31](https://cips.cardano.org/cips/cip31/))
- Inline datums in the transaction (proposed in [CIP-32](https://cips.cardano.org/cips/cip32/))
- Reference scripts in the transaction (proposed in [CIP-33](https://cips.cardano.org/cips/cip33/))

### Examples

- [Plutus V2 functionalities](https://github.com/IntersectMBO/cardano-node/blob/master/doc/reference/plutus/babbage-script-example.md)
- [How to use reference inputs](https://github.com/perturbing/vasil-tests/blob/main/reference-inputs-cip-31.md)
- [How to use inline datums](https://github.com/perturbing/vasil-tests/blob/main/inline-datums-cip-32.md)
- [How to reference scripts](https://github.com/perturbing/vasil-tests/blob/main/referencing-scripts-cip-33.md)
- [How to use collateral outputs](https://github.com/perturbing/vasil-tests/blob/main/collateral-output-cip-40.md)

### Built-in functions and types

Built-in functions and types can be introduced with just a hard fork. 
In some cases they are also available only in particular language versions.
This section indicates in which hard fork particular built-ins were introduced, and any language version constraints.

#### Alonzo

This is when the majority of the built-in types and functions were added to `PlutusV1`. 
You can find an enumeration of them in :cite[plutus-core-spec]{.title-ref}.

#### Vasil

All of the built-in types and functions from `PlutusV1` were added to `PlutusV2`.

The following built-in function was added to `PlutusV2` only (i.e., it is not available in `PlutusV1`).

- `serializeData` (proposed in [CIP-42](https://cips.cardano.org/cips/cip42/))

#### PlutusV3

Plutus and cryptography teams at IOG, in collaboration with [MLabs](https://mlabs.city/), continue to develop Plutus capabilities.
Starting with the release of [Cardano node v.8.8.0-pre](https://github.com/IntersectMBO/cardano-node/releases/tag/8.8.0-pre), `PlutusV3` is available on [SanchoNet](https://sancho.network/), introducing the Cardano community to governance features from [CIP-1694](https://cips.cardano.org/cip/CIP-1694#goal) in a controlled testnet environment.

`PlutusV3` is the new ledger language that enhances Plutus Core's cryptographic capabilities, offering the following benefits for the smart contract developer community:

- Providing an updated script context that will let users see [CIP-1694](https://cips.cardano.org/cip/CIP-1694#goal) governance-related entities and voting features
- Interoperability between blockchains
- Advanced Plutus primitives
- Well-known and optimal cryptographic algorithms
- Support for porting of smart contracts from Ethereum
- Creating sidechain bridges
- Improving performance by adding a sums of products (SOPs) feature to support the direct encoding of differrent data types.

#### Sums of products

`PlutusV3` introduces sums of products - a way of encoding data types that leads to smaller and cheaper scripts compared with [Scott encoding](https://en.wikipedia.org/wiki/Mogensen%E2%80%93Scott_encoding), a common way of encoding data types in Plutus Core.

The sums of products approach aims to boost script efficiency and improve code generation for Plutus Core compilers. 
The changes involve new term constructors for packing fields into constructor values and efficient tag inspection for case branches, potentially running programs 30% faster. 
For an in-depth discussion, see [CIP-85](https://cips.cardano.org/cip/CIP-0085).

#### New cryptographic primitives

`PlutusV3` provides new built-in primitives that expand the language's capabilities.

- **BLS12-381**: A curve pairing that includes 17 primitives that support cryptographic curves. This is a benefit to sidechain specification implementation and [Mithril](https://iohk.io/en/blog/posts/2023/07/20/mithril-nears-mainnet-release/) integration.
- **Blake2b-224**: A cryptographic hash function for on-chain computation of public-key hashes for the validation of transaction signatures. Supports community projects and contributes to Cardano's versatility.
- **Keccak-256**: A cryptographic hash function that produces a 256-bit (32-byte) hash value, commonly used for secure data verification. Supports Ethereum signature verification within scripts and cross-chain solutions.

#### Bitwise primitives

PlutusV3 initially brings several new bitwise primitives (with more to come at later stages). 
The introduction of [CIP-58](https://cips.cardano.org/cip/CIP-0058) bitwise primitives will enable the following features:

- Very low-level bit manipulations within Plutus, supporting the ability to execute high-performance data manipulation operations.
- Supporting the implementation of secure and robust cryptographic algorithms within Plutus.
- Facilitating standard, high-performance implementations for conversions between integers and bytestrings.

`PlutusV3` adds two bitwise primitives: `integerToByteString` and `byteStringToInteger`. 
The remaining primitives will be added to `PlutusV3` gradually and will not require a new ledger language.

## Upgrading to Vasil and Plutus script addresses

### A Plutus V2 script will not have the same hash value as a Plutus V1 script

DApp developers might expect that when doing a migration from `PlutusV1` scripts to `PlutusV2` scripts, the same source code, when recompiled, will generate the same hash value of that script address. 
However, it is impossible for a compiled `PlutusV2` script to have the same script hash and address as a compiled `PlutusV1` script.

Using the exact same script with different language versions will result in different hashes. 
The exact same script (as in `UPLC.Program`) can be used as a `PlutusV1` script or a `PlutusV2` script, and since the language version is part of the hash, the two hashes will be different.

### A Plutus V1 script will not necessarily have the same hash value when recompiled with a later version of the Plutus Compiler

Suppose you write your Haskell source code (Plutus Tx), compile it into Plutus Core code (PLC), generate its hash value, then use it in a transaction. 
If you don't save your compiled code, and then decide to use the same script in the future, you would have to recompile it. 
This could result in a different hash value of the script address even without upgrading from `PlutusV1` to `PlutusV2` scripts. 
This is because the hash is computed based on the output of the compiled code.

Given Plutus compiler version changes, changes in the dependencies, and multiple other improvements, it is expected that the hash value of the script address will change after the source code is recompiled.

### When to export and save the output of a compiled script

Once you expect that you will not modify the on-chain part of your application and you don't want the hash value of your script address to change, the best way to keep it the same is to save the output of your final compiled Plutus Core code (PLC) to a file.

For details on how to export scripts, please see `How to export scripts, datums and 
redeemers </howtos/exporting-a-script>`{.interpreted-text role="doc"}.

## Cost model parameters

> **Note**
> 
> The cost model parameters has been automatically generated in the Read-the-docs platform. 
> Will need to investigate what approach will make sense for Docusaurus and/or markdown files. 

The cost model for Plutus Core scripts has a number of parameters.
These are listed and briefly described below.
All of these parameters are listed in the Cardano protocol parameters and can be individually adjusted.

```
.. csv-table:: Machine parameters
   :file: ./machine-parameters.csv
   :widths: 20, 30, 40
   :header-rows: 1

.. csv-table:: Builtin parameters
   :file: ./builtin-parameters.csv
   :widths: 20, 30, 40
   :header-rows: 1
```

# Glossary

**address**  
The address of an UTXO says where the output is "going". The address stipulates the conditions for unlocking the output. This can be a public key hash, or (in the Extended UTXO model) a script hash.

**Cardano**  
The blockchain system upon which the Plutus Platform is built.

**currency**  
A class of token whose minting is controlled by a particular monetary policy script. On the Cardano ledger, there is a special currency called Ada which can never be minted and which is controlled separately.

**datum**  
The data field on script outputs in the Extended UTXO model.

**Extended UTXO Model**  
The ledger model which the Plutus Platform relies on. This is implemented in the Alonzo hard fork of the Cardano blockchain.  
See [what_is_a_ledger](#).

**minting**  
A transaction which mints tokens creates new tokens, providing that the corresponding minting policy script is satisfied. The amount minted can be negative, in which case the tokens will be destroyed instead of created.

**minting policy script**  
A script which must be satisfied in order for a transaction to mint tokens of the corresponding currency.

**Hydra**  
A Layer 2 scalability solution for Cardano. See [chakravarty2020hydra](#).

**distributed ledger**  
See [what_is_a_ledger](#).

**Marlowe**  
A domain-specific language for writing financial contract applications.

**multi-asset**  
A generic term for a ledger which supports multiple different asset types natively.

**off-chain code**  
The part of a contract application's code which runs off the chain, usually as a contract application.

**on-chain code**  
The part of a contract application's code which runs on the chain (i.e., as scripts).

**Plutus Core**  
The programming language in which scripts on the Cardano blockchain are written. Plutus Core is a small functional programming language --— a formal specification is available with further details. Plutus Core is not read or written by humans, it is a compilation target for other languages.  
See [what_is_plutus_foundation](#).

**Plutus IR**  
An intermediate language that compiles to Plutus Core. Plutus IR is not used by users, but rather as a compilation target on the way to Plutus Core. However, it is significantly more human-readable than Plutus Core, so should be preferred in cases where humans may want to inspect the program.

**Plutus Platform**  
The combined software support for writing contract applications, including:
1. Plutus Foundation, and
2. The Plutus Application Framework  
See [what_is_the_plutus_platform](#).

**Plutus Tx**  
The libraries and compiler for compiling Haskell into Plutus Core to form the on-chain part of a contract application.

**redeemer**  
The argument to the validator script which is provided by the transaction which spends a script output.

**rollback**  
The result of the local node switching to the consensus chain.

**script**  
A generic term for an executable program used in the ledger. In the Cardano blockchain, these are written in Plutus Core.

**script context**  
A data structure containing a summary of the transaction being validated, as well as a way of identifying the current script being run.

**script output**  
A UTXO locked by a script.

**token**  
A generic term for a native tradeable asset in the ledger.

**transaction output**  
Outputs produced by transactions. They are consumed when they are spent by another transaction. Typically, some kind of evidence is required to be able to spend a UTXO, such as a signature from a public key, or (in the Extended UTXO Model) satisfying a script.

**UTXO**  
An unspent transaction output.

**utxo congestion**  
The effect of multiple transactions attempting to spend the same transaction output.

**validator script**  
The script attached to a script output in the Extended UTXO model. Must be run and return positively in order for the output to be spent. Determines the address of the output.
