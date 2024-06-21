---
sidebar_position: 15
---

# Exporting scripts, datums and redeemers

> :pushpin: **NOTE**
> 
> This guide uses the scripts from the topic [Writing basic validator scripts](writing-basic-validator-scripts.md).

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

<LiteralInclude file="BasicValidators.hs" language="haskell" title="Block Title" start="-- BLOCK5" end="-- BLOCK6" />

`CompiledCode` has a different serialization method, `Flat`, but the principle is the same.

The serialized form of `CompiledCode` can also be dumped using a plugin option:

``` haskell
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-uplc #-}
```

This will dump the output to a temporary file with a name based on the module name. 
The filename will be printed to the console when compiling the source file. 
You can then move it to a more permanent location.

It can be read in conveniently with `loadFromFile` as an alternative to `compile`.

<LiteralInclude file="BasicValidators.hs" language="haskell" title="Block Title" start="-- BLOCK6" end="-- BLOCK7" />

