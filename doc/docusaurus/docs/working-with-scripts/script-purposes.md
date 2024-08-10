---
sidebar_position: 2
---

# Script Purposes

One of the arguments every Plutus script receives is the script context, containing information about the transaction the script is validating.
One of the fields of script context is the script purpose.
Since a transaction may do multiple things, each of which is validated by a separate  script, the script purpose informs a script what exactly it is supposed to validate.

Plutus V1 and V2 share the same [`ScriptPurpose`](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V1-Contexts.html#t:ScriptPurpose) type with four variants: spending, minting, rewarding and certifying.
Plutus V3's [`ScriptPurpose`](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3-Contexts.html#t:ScriptPurpose) has two additional variants: voting and proposing.
Next we go over and explain all these different script purposes.

## Spending

A spending script validates the spending of a UTXO.
A UTXO can have either a public key address or a script address.
To spend a UTXO with a script address, the script whose hash matches the script address must be included in the transaction (either directly, or as a reference script), and is executed to validate it.

The script can make the decision based on the datum attached in the UTXO being spent, if any (datum is mandatory for Plutus V1 and V2, i.e., a UTXO with a Plutus V1 or V2 script address but without a datum cannot be spent; datum is optional for Plutus V3), the redeemer included in the transaction, as well as other fields of the transaction.

The `Spending` constructor of `ScriptPurpose` contains a `TxOutRef` field, which is the UTXO the transaction is attempting to spend.

## Minting

Minting scripts, sometimes also referred to as minting policies, are used to approve or reject minting of new assets.

An asset on Cardano contains a `CurrencySymbol` and a `TokenName`.
If a transaction attempts to mint some new assets, then for each unique `CurrencySymbol` in the new assets, the script whose hash matches the `CurrencySymbol` must be included in the transaction, and is executed to validate the minting of that `CurrencySymbol`.
This is the reason why the `Minting` constructor of `ScriptPurpose` contains a `CurrencySymbol` field.

A minting script should pay attention to the fact that the transaction may attempt to mint multiple assets with the same `CurrencySymbol` but different `TokenNames`.
In general all these assets with the same `CurrencySymbol` should be checked.

## Rewarding

As previously stated, a UTXO's address can be either a public key address or a script address.
Both kinds of addresses can optionally have a staking credential.
A UTXO may contain Ada, and the Ada it contains can be delegated to an SPO to earn staking rewards.
Staking rewards are deposited into a reward account[^1] corresponding to the staking credential.

A staking credential can contain either a public key hash or a script hash.
To withdraw rewards from a reward account corresponding to a staking credential that contains a script hash, the script with that particular hash must be included in the transaction, and is executed to validate the withdrawal.

For example, such a script may check that any withdrawal must not take more than 10 Ada at a time, and that any withdrawal must be deposited into one of the allowed addresses.

## Certifying

A certifying script validates one of the following actions a transaction attempts to make: (1) registering a staking credential, and in doing so, creating a reward account associated with the staking credential; (2) de-registering a staking credential, and in doing so, terminating the reward account; (3) delegating a staking credential to a particular delegatee.

In all three cases, if the staking credential in question contains a script hash (as opposed to a public key hash), the script with that hash must be included in the transaction, and is executed to validate the action.

Such a script may, for instance, check that certain signatures be provided for registration, de-registration and delegation, or that the delegatee must be among the allowed delegatees.

## Voting

A voting script validates votes cast by a DRep or a constitutional committee member in a transaction.
A DRep or a constitution committee member can be associated with a script hash.
If a transaction contains one or more votes from a DRep or a constitution committee member associated with a script hash, the script with that hash must be included in the transaction, and is executed to approve or reject the vote.

## Proposing

A proposing script, also known as constitution script or guardrail script, validates two kinds of [governance actions](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3-Contexts.html#t:ScriptContext): `ParameterChange` and `TreasuryWithdrawals`.

There is a key distinction between proposing scripts and other kinds of scripts: proposing scripts are not written by regular users.
At any given point in time, there is exactly one active proposing script being used by the entire chain.
This proposing script must be included in transactions that propose `ParameterChange` or `TreasuryWithdrawals`.
The ledger enforces that no other proposing script is accepted.
The proposing script is updated only when there is a change to the constitution, via the `NewConstitution` governance action.

Note that what the proposing script decides is whether the _proposal_ of a governance action is allowed to go through, rather than whether the governance action will be enacted.
After a proposal goes through, it will need to meet the appropriate criteria (such as gathering enough votes from consitution committee members, DReps and/or SPOs) in order to be enacted.

---

[^1]: Reward accounts are distinct from UTXOs, and are more akin to accounts in account-based blockchains.
They are used for accumulating staking rewards, rather than using UTXOs, in order to avoid creating a large number of UTXOs with tiny values.
Reward accounts are special on Cardano and cannot be created arbitrarily.
Each reward account is associated with a staking credential, and is created automatically when the staking credential is registered.
