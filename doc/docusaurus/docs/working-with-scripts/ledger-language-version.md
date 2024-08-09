---
sidebar_position: 1
---

# Plutus Ledger Language Version (Plutus V1/V2/V3)

As explained in [Different Notions of Version](../essential-concepts/versions.md), Plutus V1, V2 and V3 are not different programming languages; the main difference lies in the arguments the script receives from the ledger, and the return value of the script.
Therefore, Plutus V1, V2 and V3 are, in essence, type signatures, in the sense that they each comprise a subset of Untyped Plutus Core (UPLC) programs with certain types.
Any UPLC program that expects certain arguments and returns a certain value can be considered and used as a Plutus V1 (resp. V2 and V3) script.

Next we first briefly discuss the script context, and then explain these type signatures in detail.

## ScriptContext

Every Plutus script receives an argument called script context.
It contains information about the transaction the script is validating, such as inputs, outputs, transaction fee, signatures and so on.
Additionally, since a transaction may have multiple things to validate (e.g., it may be spending multiple script UTXOs, or performing both spending and minting), each of which is validated by a separate script, the script context also has a script purpose field, telling the script what exactly it is supposed to validate.

Plutus V1, V2 and V3 scripts receive different script contexts even when all else is equal.
This is because different ledger language versions are introduced in different ledger eras; transactions in different ledger eras have different fields - a new era usually adds new fields and may also change existing fields.
As a result, The script contexts for Plutus V1, V2 and V3 also have different fields, leading to different Haskell types ([V1](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V1-Contexts.html#t:ScriptContext), [V2](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V2-Contexts.html#t:ScriptContext), [V3](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3-Contexts.html#t:ScriptContext)).
We cannot modify the script context fields of an existing ledger language version once it is published, since it would break existing scripts.

In general, a ledger language version cannot be used in a transaction, if the ledger language version was introduced in ledger era A, the transaction uses features in ledger era B, and A is earlier than B.
For instance, Plutus V1 (introduced in the Alonzo era) scripts cannot be used in a transaction which utilizes inline datum (a Babbage era feature); Plutus V2 (introduced in the Babbage era) scripts cannot be used in a transaction that registers a DRep (introduced in the Conway era)[^1].


## Plutus V1 and Plutus V2

<!--- TODO: link to the page explaining script purposes, once there is one --->

Plutus V1 and Plutus V2 scripts have four [script purposes](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V1-Contexts.html#t:ScriptPurpose): spending, minting, certifying, and rewarding.
The arguments a Plutus V1 or V2 script receives depend on the script purpose.
There is no requirement on the return value of a Plutus V1 and V2 script: script evaluation succeeds as long as the evaluation terminates without error, and the execution budget is not exceeded.

### Spending Scripts

A Plutus V1/V2 spending script receives three arguments corresponding to datum, redeemer and script context.
All arguments are encoded as `BuiltinData`.
Thus in Plutux Tx, a spending script has the following type:

```haskell
BuiltinData -> BuiltinData -> BuiltinData -> any
```

To create a Plutus script using Plutus Tx, it is common to first write a function that takes the corresonding Haskell domain types and returns `Bool`.
For example, the following function can be used to implement the main business logic of a Plutus V1 spending script:

```haskell
myV1SpendingScriptTyped :: MyDatum -> MyRedeemer -> PlutusLedgerApi.V1.ScriptContext -> Bool
```

where `MyDatum` and `MyRedeemer` are your user-defined Haskell types specific to your contract.
If you are writing a Plutus V2 script, use `PlutusLedgerApi.V2.ScriptContext`.

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

In this example the script happens to return `BuiltinUnit`, but this is not a requirement for Plutus V1 or V2.

### Minting, Certifying and Rewarding Scripts

Unlike spending scripts, Plutus V1 and V2 scripts for minting, certifying and rewarding purposes take one fewer argument: there is no datum argument.
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

## Plutus V3

Plutus V3 has two additional [script purposes](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3-Contexts.html#t:ScriptPurpose) for validating governance actions: voting and proposing.

Besides the usual differences between different Plutus ledger language versions, there are three additional key differences between Plutus V3 and V1/V2:

<!--- TODO: link to Haddock --->
1. All Plutus V3 scripts, regardless of script purpose, take a single argument: script context.
   The datum (for spending scripts) and the redeemer are part of the Plutus V3 script context.
   This means the same script can be used for spending validation and for different purposes.
2. The datum is now optional for spending scripts.
   The script context may or may not contain a datum, depending on whether the UTXO being spent has a datum associated with it.
3. There is an additional condition for the evaluation of a Plutus V3 script to be considered successful: the return value must be a `BuiltinUnit`.

Points 1 and 2 are attributed to CIP-69, and point 3 CIP-0117.

In other words, all Plutus V3 scripts should have the following type in Plutus Tx:

```haskell
BuiltinData -> BuiltinUnit
```

Updating a Plutus V1/V2 script to turn it into a Plutus V3 script mostly involves straightforward refactoring, except that for a spending script, the case where the datum is absent will need to be handled.

---

[^1]: There is one exception to this: Plutus V1 can be used in transactions with reference inputs, even though reference inputs were introduced in the Babbage era.
