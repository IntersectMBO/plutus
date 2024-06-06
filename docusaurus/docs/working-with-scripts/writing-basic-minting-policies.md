---
sidebar_position: 10
---

# Writing basic minting policies

[Minting policy scripts](../reference/glossary.md#minting-policy-script) are the programs that can be used to control the minting of new assets on the chain. 
Minting policy scripts are much like [validator scripts](../reference/glossary.md#validator-script), and they are written similarly, so please review [Writing basic validator scripts](writing-basic-validator-scripts.md) before reading this topic. 

## Minting policy arguments

Minting policies, like validators, receive some information from the validating node:

- The [redeemer](../reference/glossary.md#redeemer), which is some script-specific data specified by the party performing the minting.
- The [script context](../reference/glossary.md#script-context), which contains a representation of the spending transaction, as well as the hash of the minting policy which is currently being run.

The minting policy is a function which receives these two inputs as *arguments*. The validating node is responsible for passing them in and running the minting policy. 
As with validator scripts, the arguments are passed encoded as `PlutusCore.Data.Data`.

## Plutus script context versions

Minting policies have access to the [script context](../reference/glossary.md#script-context) as their second argument. 
Each version of Plutus minting policy scripts are differentiated only by their `ScriptContext` argument.

> See this example from the file `MustSpendScriptOutput.hs` (lines 340 to 422) showing code addressing [Versioned Policies for both Plutus V1 and Plutus V2](https://github.com/IntersectMBO/plutus-apps/blob/05e394fb6188abbbe827ff8a51a24541a6386422/plutus-contract/test/Spec/TxConstraints/MustSpendScriptOutput.hs#L340-L422).

Minting policies tend to be particularly interested in the `mint` field, since the point of a minting policy is to control which tokens are minted.

It is also important for a minting policy to look at the tokens in the `mint` field that use its own currency symbol i.e. policy hash. 
Note that checking only a specific token name is usually not correct. 
The minting policy must check for correct minting (or lack there of) of all token names under its currency symbol. 
This requires the policy to refer to its own hash&mdash;fortunately this is provided for us in the script context of a minting policy.

## Writing minting policies

Here is an example that puts this together to make a simple policy that allows anyone to mint the token so long as they do it one token at a time. 
To begin with, we'll write a version that works with structured types.

<LiteralInclude file="BasicPolicies.hs" language="haskell" title="Example simple minting policy" start="-- BLOCK1" end="-- BLOCK2" />

However, scripts are actually given their arguments as type `Data`, and must signal failure with `error`, so we need to wrap up our typed version to use it on-chain.

<LiteralInclude file="BasicPolicies.hs" language="haskell" title="Example of wrapping a typed version" start="-- BLOCK2" end="-- BLOCK3" />

## Other policy examples

Probably the simplest useful policy is one that requires a specific key to have signed the transaction in order to do any minting. 
This gives the key holder total control over the supply, but this is often sufficient for asset types where there is a centralized authority.

<LiteralInclude file="BasicPolicies.hs" language="haskell" title="Policy example" start="-- BLOCK3" end="-- BLOCK4" />

> :pushpin: **NOTE**
> 
> We don't need to check that this transaction actually mints any of our asset type: the ledger rules ensure that the minting policy will only be run if some of that asset is being minted.

