---
sidebar_position: 1
---

# Plutus Ledger Language Version (Plutus V1/V2/V3)

As explained in [Different Notions of Version](../essential-concepts/versions.md), Plutus V1, V2 and V3 are not distinct programming languages; the primary difference lies in the arguments the script receives from the ledger, and the value it returns.
Therefore, Plutus V1, V2 and V3 can be understood as type signatures, in the sense that they each represent a subset of Untyped Plutus Core (UPLC) programs with specific types.
Any UPLC program that matches the expected argument and return types can be considered and used as a Plutus V1, V2 or V3 script.

Next we'll start with a brief overview of the script context, followed by an in-depth explanation of these type signatures.

## ScriptContext

Every Plutus script receives an argument called script context.
It contains information about the transaction the script is validating, such as inputs, outputs, transaction fee, signatures and so on.
Additionally, since a transaction may have multiple things to validate (e.g., it may be spending multiple script UTXOs, or performing both spending and minting), each of which is validated by a separate script, the script context also has a script purpose field, telling the script what exactly it is supposed to validate.

Plutus V1, V2 and V3 scripts receive different script contexts even when all else is equal.
This is because different ledger language versions are introduced in different ledger eras; transactions in different ledger eras have different fields - a new era usually adds new fields and may also change existing fields.
As a result, The script contexts for Plutus V1, V2 and V3 also have different fields, leading to different Haskell types ([V1](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V1-Contexts.html#t:ScriptContext), [V2](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V2-Contexts.html#t:ScriptContext), [V3](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3-Contexts.html#t:ScriptContext)).
We cannot modify the script context fields of an existing ledger language version once it is published, since it would break existing scripts.

In general, a ledger language version cannot be used in a transaction, if the ledger language version was introduced in ledger era A, the transaction uses features in ledger era B, and A is earlier than B.
For instance, Plutus V1 (introduced in the Alonzo era) scripts cannot be used in a transaction which utilizes inline datums (a Babbage era feature); Plutus V2 (introduced in the Babbage era) scripts cannot be used in a transaction that registers a DRep (introduced in the Conway era)[^1].


## Plutus V1

Plutus V1 is the initial ledger language version, enabled at the Alonzo hard fork, a hard fork that introduced the Alonzo era.

Plutus V1 scripts have four [script purposes](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V1-Contexts.html#t:ScriptPurpose): spending, minting, certifying, and rewarding[^2].
The arguments a Plutus V1 script receives depend on the script purpose.
There is no requirement on the return value of a Plutus V1 script: script evaluation succeeds as long as the evaluation terminates without error, and the execution budget is not exceeded.

### Spending Scripts

A Plutus V1 spending script receives three arguments corresponding to datum, redeemer and script context.
All arguments are encoded as `BuiltinData`.
Thus in Plutus Tx, a spending script has the following type:

```haskell
BuiltinData -> BuiltinData -> BuiltinData -> any
```

To create a Plutus script using Plutus Tx, it is common to first write a function that takes the corresponding Haskell domain types and returns `Bool`.
For example, the following function can be used to implement the main business logic of a Plutus V1 spending script:

```haskell
myV1SpendingScriptTyped :: MyDatum -> MyRedeemer -> PlutusLedgerApi.V1.ScriptContext -> Bool
```

where `MyDatum` and `MyRedeemer` are your user-defined Haskell types specific to your contract.

From `myV1SpendingScriptTyped`, you can obtain `BuiltinData -> BuiltinData -> BuiltinData -> any`, and subsequently compile it to UPLC, via

```haskell
myV1SpendingScriptUntyped :: BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit
myV1SpendingScriptUntyped myDatum myRedeemer scriptContext =
  PlutusTx.Prelude.check
    ( myV1SpendingScriptTyped
        (PlutusTx.unsafeFromBuiltinData myDatum)
        (PlutusTx.unsafeFromBuiltinData myRedeemer)
        (PlutusTx.unsafeFromBuiltinData scriptContext)
    )

myV1SpendingScriptCompiled :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit)
myV1SpendingScriptCompiled = $$(PlutusTx.compile [||myV1SpendingScriptUntyped||])
```

`unsafeFromBuiltinData` is a method from the [`UnsafeFromData`](http://localhost:3000/docs/working-with-scripts/ledger-language-version) class.
Each call to `unsafeFromBuiltinData` decodes a `BuiltinData` into a value of a Haskell domain type, failing if the conversion fails.
The `check` function takes a `Bool` and returns a `BuiltinUnit`, throwing an error if the input is `False`.
It is needed because returning `False` does not cause the validation to fail; to fail the validation, an error needs to be thrown.

In this example the script happens to return `BuiltinUnit`, but this is not a requirement for Plutus V1.

### Minting, Certifying and Rewarding Scripts

Unlike spending scripts, Plutus V1 scripts for minting, certifying and rewarding purposes take one fewer argument: there is no datum argument.
Thus in Plutus Tx, a minting, certifying or rewarding script should have the following type:

```haskell
BuiltinData -> BuiltinData -> any
```

Since this type signature is shared by minting, certifying and rewarding scripts, the same script can be used for multiple of these three purposes, for example

```haskell
myV1MintingAndRewardingScriptTyped :: MyRedeemer -> PlutusLedgerApi.V1.ScriptContext -> Bool
myV1MintingAndRewardingScriptTyped myRedeemer scriptContext =
  case scriptContextPurpose scriptContext of
    Minting cs -> -- Perform minting validation
    Rewarding cred -> -- Perform rewarding validation
```

Because spending scripts take one more argument, the same script cannot be used both for spending validation and for a different purpose (minting, certifying or rewarding).

### Script Evaluation and Unsaturated Scripts

As said before, evaluating a Plutus V1 and V2 script succeeds as long as the evaluation terminates without error, and the budget is not exceeded.

This means, crucially, that an unsaturated script (a script expecting more arguments than it receives) succeeds trivially, since the evaluation terminates almost immediately and returns a lambda.
Thus be careful: if, for example, you accidentally use a spending script (which expects three arguments) as a minting script (which will receive two arguments), it will always succeed, which is obviously not what you want.

## Plutus V2

Plutus V2 was enabled at the Vasil hard fork, which introduced the Babbage era.

Plutus V2 shares several similarities with Plutus V1:
- It supports the same four script purposes.
- The number of arguments a Plutus V2 script receives is identical to Plutus V1: three for spending scripts, and two for other script purposes.
- Script evaluation succeeds as long as no errors occur and the budget is not exceeded.

The differences between Plutus V1 and Plutus V2 include:
- Plutus V2 can be used in transactions that utilizes Babbage era features like [inline datums](https://cips.cardano.org/cip/CIP-0032) and [collateral output](https://cips.cardano.org/cip/CIP-0040), while Plutus V1 cannot (except for reference scripts, as noted earlier).
- Plutus V2's script context contains more fields than Plutus V1 due to new transaction features.
  When writing a Plutus V2 script, you should use the `ScriptContext` data type from `PlutusLedgerApi.V2`.
- For now, Plutus V2 supports more builtin functions than Plutus V1, including `serialiseData`, `verifyEcdsaSecp256k1Signature` and `verifySchnorrSecp256k1Signature`.
  However, as explained in [Different Notions of Version](../essential-concepts/versions.md), we plan to enable all builtin functions across all ledger language versions in the future.

## Plutus V3

Plutus V3 was enabled at the Chang hard fork, which introduced the Conway era.

Plutus V3 has two additional [script purposes](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3-Contexts.html#t:ScriptPurpose) for validating governance actions: voting and proposing.

Additional key differences between Plutus V3 and V1/V2 include:

1. All Plutus V3 scripts, regardless of script purpose, take a single argument: the script context.
   The datum (for spending scripts) and the redeemer are part of the Plutus V3 script context.
   This means the same script can be used for spending validation and for different purposes.
2. The datum is now optional for spending scripts.
   The script context may or may not contain a datum, depending on whether the UTXO being spent has a datum associated with it.
3. There is an additional condition for the evaluation of a Plutus V3 script to be considered successful: the return value must be a `BuiltinUnit`.
4. For now, Plutus V3 supports Plutus Core 1.1.0, a Plutus Core language version that introduced [sums-of-products](https://cips.cardano.org/cip/CIP-0085), as well as more builtin functions than Plutus V2.
   However, we plan to enable all Plutus Core versions and all builtin functions across all ledger language versions in the future.

The first two points above are attributed to [CIP-69](https://developers.cardano.org/docs/governance/cardano-improvement-proposals/cip-0069/), whereas the third point is attributed to [CIP-117](https://developers.cardano.org/docs/governance/cardano-improvement-proposals/cip-0117/).

In other words, all Plutus V3 scripts should have the following type in Plutus Tx:

```haskell
BuiltinData -> BuiltinUnit
```

Updating a Plutus V1/V2 script to turn it into a Plutus V3 script mostly involves straightforward refactoring, except that for a spending script, the case where the datum is absent will need to be handled.

---

[^1]: There is one exception to this: Plutus V1 can be used in transactions with reference scripts, even though reference scripts were introduced in the Babbage era.

[^2]: For more information on script purposes, refer to [Script Purposes](script-purposes.md).
