---
sidebar_position: 20
---

# Plutus Tx code

Recall that Plutus Tx is a subset of Haskell. 
It is the source language one uses to write Plutus validators. 
A Plutus Tx program is compiled into Plutus Core, which is interpreted on-chain. 
The full Plutus Tx code for the auction smart contract can be found at [AuctionValidator.hs](https://github.com/IntersectMBO/plutus-tx-template/blob/main/app/AuctionValidator.hs).

<!-- will need to update the link and file location for the new docs platform implementation -->

## Data types

First, let's define the following data types and instances for the validator:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Data types" start="-- BLOCK1" end="-- BLOCK2" />

The purpose of `makeLift` and `unstableMakeIsData` will be explained later.

Typically, writing a Plutus Tx validator script for a smart contract involves four data types:

### 1. Contract parameters

These are fixed properties of the contract. 
In our example, it is the `AuctionParams` type, containing properties like seller and minimum bid.

### 2. Datum

This is part of a script UTXO. 
It should be thought of as the state of the contract. 
Our example requires only one piece of state: the current highest bid. 
We use the `AuctionDatum` type to represent this.

### 3. Redeemer

This is an input to the Plutus script provided by the transaction that is trying to spend a script UTXO. 
If a smart contract is regarded as a state machine, the redeemer would be the input that ticks the state machine. 
In our example, it is the `AuctionRedeemer` type: one may either submit a new bid, or request to close the auction and pay out the winner and the seller, both of which lead to a new state of the auction.

### 4. Script context

This type contains the information of the transaction that the validator can inspect. 
In our example, our validator verifies several conditions of the transaction; e.g., if it is a new bid, then it must be submitted before the auction's end time; the previous highest bid must be refunded to the previous bidder, etc.

The script context type is fixed for each Plutus language version.
For Plutus V2, for example, it is `PlutusLedgerApi.V2.Contexts.ScriptContext`.

> :pushpin: **NOTE**
> 
> When writing a Plutus validator using Plutus Tx, it is advisable to turn off Haskell's `Prelude`. 
> Usage of most functions and methods in `Prelude` should be replaced by their counterparts in the `plutus-tx` library, e.g., `PlutusTx.Eq.==`.

## Main validator function

Now we are ready to introduce our main validator function. 
The beginning of the function looks like the following:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Main validator function" start="-- BLOCK2" end="-- BLOCK3" />

Depending on whether this transaction is attempting to submit a new bid or to request payout, the validator validates the corresponding set of conditions.

### Sufficient bid condition

The `sufficientBid` condition verifies that the bid amount is sufficient:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Sufficient bid condition" start="-- BLOCK3" end="-- BLOCK4" />

### Valid bid time condition

The `validBidTime` condition verifies that the bid is submitted before the auction's deadline:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Valid bid time condition" start="-- BLOCK4" end="-- BLOCK5" />

Here, `to x` is the time interval ending at `x`, i.e., `(-∞, x]`.
`txInfoValidRange` is a transaction property. 
It is the time interval in which the transaction is allowed to go through phase-1 validation.
`contains` takes two time intervals, and checks that the first interval completely includes the second. 
Since the transaction may be validated at any point in the `txInfoValidRange` interval, we need to check that the entire interval lies within `(-∞, apEndTime params]`.

The reason we need the `txInfoValidRange` interval instead of using the exact time the transaction is validated is due to [determinism](https://iohk.io/en/blog/posts/2021/09/06/no-surprises-transaction-validation-on-cardano/).
Using the exact time would be like calling a `getCurrentTime` function and branching based on the current time. 
On the other hand, by using the `txInfoValidRange` interval, the same interval is always used by the same transaction.

### Refunds previous highest bid condition

The `refundsPreviousHighestBid` condition checks that the transaction pays the previous highest bid to the previous bidder:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Refunds previous highest bid condition" start="-- BLOCK5" end="-- BLOCK6" />

It uses `PlutusTx.find` to find the transaction output (a UTXO) that pays to the previous bidder the amount equivalent to the previous highest bid, and verifies that there is at least one such output.

`lovelaceValue amt` constructs a `Value` with `amt` Lovelaces (the subunit of the Ada currency). 
`Value` is a multi-asset type that represents a collection of assets, including Ada. 
An asset is identified by a (symbol, token) pair, where the symbol represents the policy that controls the minting and burning of tokens, and the token represents a particular kind of token manipulated by the policy.
`(adaSymbol, adaToken)` is the special identifier for Ada/Lovelace.

### Correct new datum condition

The `correctNewDatum` condition verifies that the transaction produces a *continuing output* containing the correct datum (the new highest bid):

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Correct new datum condition" start="-- BLOCK6" end="-- BLOCK7" />

A "continuing output" is a transaction output that pays to the same script address from which we are currently spending. 
Exactly one continuing output must be present in this example so that the next bidder can place a new bid. 
The new bid, in turn, will need to spend the continuing output and get validated by the same validator script.

If the transaction is requesting a payout, the validator will then verify the other three conditions: `validPayoutTime`,`sellerGetsHighestBid` and `highestBidderGetsAsset`. 
These conditions are similar to the ones already explained, so their details are omitted.

### Compiling the validator

Finally, we need to compile the validator written in Plutus Tx into Plutus Core, using the Plutus Tx compiler:

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="Compiling the validator" start="-- BLOCK8" end="-- BLOCK9" />

The type of the compiled validator is `CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())`, where type `BuiltinData -> BuiltinData -> BuiltinData -> ()` is also known as the *untyped validator*. 
An untyped validator takes three `BuiltinData` arguments, representing the serialized datum, redeemer, and script context. 
The call to `PlutusTx.unsafeFromBuiltinData` is the reason we need the `PlutusTx.unstableMakeIsData` shown before, which derives `UnsafeFromData` instances. 
And instead of returning a `Bool`, it simply returns `()`, and the validation succeeds if the script evaluates without error.

Note that `AuctionParams` is an argument of neither the untyped validator nor the final UPLC program. 
`AuctionParams` contains contract properties that don't change, so it is simply built into the validator.

Since the Plutus Tx compiler compiles `a` into `CompiledCode a`, we first use `auctionUntypedValidator` to obtain an untyped validator. 
It takes `AuctionParams`, and returns an untyped validator. 
We then define the `auctionValidatorScript` function, which takes `AuctionParams` and returns the compiled Plutus Core program.

To create the Plutus validator script for a particular auction, we call `auctionValidatorScript` with the appropriate `AuctionParams`. 
We will then be able to launch the auction on-chain by submitting a transaction that outputs a script UTXO with `Nothing` as the datum.

> :pushpin: **NOTE**
> 
> It is worth noting that we must call `PlutusTx.compile` on the entire `auctionUntypedValidator`, rather than applying it to `params` before compiling, as in `$$(PlutusTx.compile [||auctionUntypedValidator params||])`. 
> The latter won't work, because everything being compiled (inside `[||...||]`) must be known at compile time, but `params` is not: it can differ at runtime depending on what kind of auction we want to run. 
> Instead, we compile the entire `auctionUntypedValidator` into Plutus Core, then use `liftCode` to lift `params` into a Plutus Core term, and apply the compiled `auctionUntypedValidator` to it at the Plutus Core level. 
> To do so, we need the `Lift` instance for `AuctionParams`, derived via `PlutusTx.makeLift`.

