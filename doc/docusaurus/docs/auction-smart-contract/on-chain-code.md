---
sidebar_position: 5
---

# On-chain Code: The Auction Validator

:::caution
The code in this example is not a production-ready implementation, as it is not optimized for security or efficiency.
It is provided purely as an example for illustration and educational purposes.
Refer to resources like **[Cardano Plutus Script Vulnerability Guide](https://library.mlabs.city/common-plutus-security-vulnerabilities)** for best practices on developing secure smart contracts.
:::

# Auction Properties

In this example, a seller wants to auction some asset she owns, represented as a non-fungible token (NFT) on Cardano.
She would like to create and deploy an auction smart contract with the following properties:

- there is a minimum bid amount
- each bid must be higher than the previous highest bid (if any)
- once a new bid is made, the previous highest bid (if exists) is immediately refunded
- there is a deadline for placing bids; once the deadline has passed, new bids are no longer accepted, the asset can be transferred to the highest bidder (or to the seller if there are no bids), and the highest bid (if exists) can be transferred to the seller.

# Plinth Code

Plinth is a subset of Haskell, used to write on-chain code, also known as validators or scripts.
A Plinth program is compiled into Plutus Core, which is interpreted on-chain.
The full Plinth code for the auction smart contract can be found at [AuctionValidator.hs](https://github.com/IntersectMBO/plutus-tx-template/blob/main/src/AuctionValidator.hs).

<!-- will need to update the link and file location for the new docs platform implementation -->

## Data types

First, let's define the following data types and instances for the validator:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Data types" start="-- BLOCK1" end="-- BLOCK2" />

The purpose of `makeLift` and `makeIsDataSchemaIndexed` will be explained later.

Writing a Plinth validator script for a smart contract often involves the following data types:

### 1. Contract parameters

These are fixed properties of the contract. You can put here values that will never change during the contract's life cycle.
In our example, it is the `AuctionParams` type, containing properties like seller and minimum bid.

### 2. Datum

This is part of a script UTXO.
It's commonly used to hold the state of the contract and values that can change throughout the contract's life cycle.
Our example requires only one piece of state: the current highest bid.
We use the `AuctionDatum` type to represent this.

### 3. Redeemer

This is an input to the Plutus script provided by the transaction that is trying to spend a script UTXO.
If a smart contract is regarded as a state machine, the redeemer would be the input that ticks the state machine.
In our example, it is the `AuctionRedeemer` type: one may either submit a new bid, or request to close the auction and pay out the winner and the seller, both of which lead to a new state of the auction.

### 4. Script context

This type contains the information of the transaction that the validator can inspect.
In our example, our validator verifies several conditions of the transaction; e.g., if it is a new bid, then it must be submitted before the auction's end time; the previous highest bid must be refunded to the previous bidder, etc.

Different [ledger language versions](../working-with-scripts/ledger-language-version.md) use different script context types.
In this example we are writing a Plutus V3 scripts, so we import the `ScriptContext` data type from `PlutusLedgerApi.V3.Contexts`.

> :pushpin: **NOTE**
>
> When writing a Plutus validator using Plinth, it is advisable to turn off Haskell's `Prelude`. One way of doing it is the GHC extension `NoImplicitPrelude` enabled in the module header.
> Usage of most functions and methods in `Prelude` should be replaced by their counterparts in the `plutus-tx` library, e.g., instead of the `==` from `base`, use `PlutusTx.Eq.==`.

## Main Validator Function

Now we are ready to introduce our main validator function.
The beginning of the function looks like the following:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Main validator function" start="-- BLOCK2" end="-- BLOCK3" />

Depending on whether this transaction is attempting to submit a new bid or to request payout, the validator validates the corresponding set of conditions.

### Sufficient Bid Condition

The `sufficientBid` condition verifies that the bid amount is sufficient:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Sufficient bid condition" start="-- BLOCK3" end="-- BLOCK4" />

### Valid Bid Time Condition

The `validBidTime` condition verifies that the bid is submitted before the auction's deadline:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Valid bid time condition" start="-- BLOCK4" end="-- BLOCK5" />

Here, `to x` is the time interval ending at `x`, i.e., `(-∞, x]`.
`txInfoValidRange` is a transaction property.
It is the time interval in which the transaction is allowed to go through phase-1 validation.
`contains` takes two time intervals, and checks that the first interval completely includes the second.
Since the transaction may be validated at any point in the `txInfoValidRange` interval, we need to check that the entire interval lies within `(-∞, apEndTime params]`.

The reason a script receives the `txInfoValidRange` interval instead of the exact time the script is run is due to [determinism](https://iohk.io/en/blog/posts/2021/09/06/no-surprises-transaction-validation-on-cardano/).
Using the exact time would be like calling a `getCurrentTime` function and branching based on the current time.
On the other hand, by using the `txInfoValidRange` interval, the same interval is always used by the same transaction.
If the current time when the transaction is validated is outside of the interval, the transaction is rejected immediately without running the script.

Also note the tilde (`~`) in `~validBidTime = ...`.
When writing Plinth it is [advisable](../using-plinth/compiling-plinth.md) to turn on the `Strict` extension, which generally improves script performance.
Doing so makes all bindings strict, which means, in this particular case, without the `~`, `validBidTime` would be evaluated even if the redeemer matches the `Payout` case, which doesn't need this condition.
Doing so results in unnecessary work or even unexpected evaluation failures.
The `~` makes `validBidTime` non-strict, i.e., only evaluated when used.

On the other hand, it is unnecessary to add `~` to `sufficientBid`, since it has a function type, and a function cannot be evaluated further without receiving enough arguments.

### Refunds Previous Highest Bid Condition

The `refundsPreviousHighestBid` condition checks that the transaction pays the previous highest bid to the previous bidder:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Refunds previous highest bid condition" start="-- BLOCK5" end="-- BLOCK6" />

It uses `PlutusTx.find` to find the transaction output (a UTXO) that pays to the previous bidder the amount equivalent to the previous highest bid, and verifies that there is at least one such output.

### Correct Output Condition

The `correctOutput` condition verifies that the transaction produces a *continuing output* (see below for definition) containing the correct datum and value.
It has two subconditions:

- `correctOutputDatum`: the datum should contain the new highest bid
- `correctOutputValue`: the value should contain (1) the token being auctioned, and (2) the bid amount.

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Correct new datum condition" start="-- BLOCK6" end="-- BLOCK7" />

A "continuing output" is a transaction output that pays to the same script address from which we are currently spending.
Exactly one continuing output must be present in this example so that the next bidder can place a new bid.
The new bid, in turn, will need to spend the continuing output and get validated by the same script.

If the transaction is requesting a payout, the validator will then verify the other three conditions: `validPayoutTime`, `sellerGetsHighestBid` and `highestBidderGetsAsset`.
These conditions are similar to the ones already explained, so their details are omitted.

### Compiling the validator

Finally, we need to compile the validator written in Plinth into Plutus Core, using the Plinth compiler:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Compiling the validator" start="-- BLOCK8" end="-- BLOCK9" />

The type of a compiled Plutus V3 spending validator should be `CompiledCode (BuiltinData -> BuiltinUnit)`, as explained in [Plutus Ledger Language Version](../working-with-scripts/ledger-language-version.md).
The call to `PlutusTx.unsafeFromBuiltinData` is the reason we need the `PlutusTx.unstableMakeIsData` shown before, which derives `UnsafeFromData` instances.
And instead of returning a `Bool`, it returns `BuiltinUnit`, and the validation succeeds if the script evaluates without error.

Note that `AuctionParams` is _not_ an argument of the compiled validator.
`AuctionParams` contains contract properties that don't change, so it is simply built into the validator by partial application.
The partial application is done via `PlutusTx.unsafeApplyCode`.

> :pushpin: **NOTE**
>
> It is worth noting that we must call `PlutusTx.compile` on the entire `auctionUntypedValidator`, rather than applying it to `params` before compiling, as in `$$(PlutusTx.compile [||auctionUntypedValidator params||])`.
> The latter won't work, because everything being compiled (inside `[||...||]`) must be known at compile time, but we won't be able to access `params` until runtime.
> Instead, once we have the `params` value at runtime, we use `liftCodeDef` or `liftCode` to lift it into a Plutus Core term before calling `unsafeApplyCode`.
> This is the reason why we need the `Lift` instance for `AuctionParams`, derived via `PlutusTx.makeLift`.
