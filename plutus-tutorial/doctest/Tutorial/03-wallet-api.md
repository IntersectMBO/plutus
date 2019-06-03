# Wallet API II: Smart Contracts

This tutorial shows how to implement a crowdfunding campaign as a Plutus contract, using the wallet API to submit it to the blockchain. It is the third in a series of tutorials on Plutus smart contracts.

1. [Plutus Tx](./01-plutus-tx.md)
2. [A guessing game](./02-validator-scripts.md)
3. A crowdfunding campaign (this tutorial)
4. [Working with the emulator](../../tutorial/Tutorial/Emulator.hs)
5. [A multi-stage contract](../../tutorial/Tutorial/Vesting.hs)

You can run this code in the [Plutus Playground](https://prod.playground.plutus.iohkdev.io/) - see Section 2.1, "Testing the contract in the Playground".

We assume the reader is familiar with the [UTxO model with scripts](../../../docs/extended-utxo/README.md) and the [first](./01-plutus-tx.md) [two](./02-validator-scripts.md) tutorials.

**WARNING** The wallet API and by extension the wallet API tutorial is a work in progress and may be changed without much warning.

The tutorial has three parts. In part 1 we write the contract, including all the data types we need, validator scripts, and contract endpoints that handle the interactions between wallet and blockchain. In part 2 we show how to test the contract. Part 3 contains a number of questions and exercises related to this contract.

# 1. Contract Definition

We need the same language extensions and imports as [before](./02-validator-scripts.md):

```haskell
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE NoImplicitPrelude   #-}
module Tutorial.WalletAPI where

import           Language.PlutusTx.Prelude
import qualified Language.PlutusTx            as PlutusTx
import qualified Ledger.Interval              as I
import qualified Ledger.Slot                  as S
import           Ledger                       (Address, DataScript(..), PubKey(..), RedeemerScript(..), Signature(..), Slot(..), TxId, ValidatorScript(..))
import qualified Ledger                       as L
import qualified Ledger.Ada                   as Ada
import           Ledger.Ada                   (Ada)
import qualified Ledger.Value                 as Value
import           Ledger.Value                 (Value)
import           Ledger.Validation            (PendingTx(..), PendingTxIn(..), PendingTxOut)
import qualified Ledger.Validation            as V
import           Wallet                       (WalletAPI(..), WalletDiagnostics(..), MonadWallet, EventHandler(..), EventTrigger)
import qualified Wallet                       as W
import           GHC.Generics                 (Generic)
```

## 1.1 Data Types

The crowdfunding campaign has the following parameters:

* Funding target
* End date
* Collection deadline
* Campaign owner

If the funding target is reached at the end date, then the campaign owner may collect all the funds. If it isn't reached, or if the owner does not collect the funds before the collection deadline, then the contributors are entitled to a refund.

In Haskell:

```haskell
data Campaign = Campaign {
      fundingTarget      :: Ada,
      endDate            :: Slot,
      collectionDeadline :: Slot,
      campaignOwner      :: PubKey
 }
```

The type of Ada values is [`Ada`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Ledger-Ada.html#v:Ada). Dates are expressed in terms of slots, and their type is [`Slot`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Ledger-Slot.html#v:Slot). The campaign owner is identified by their public key.

Just like we did in the [guessing game](./02-validator-scripts.md), we need to call `makeLift` for data types that we want to convert to Plutus at Haskell runtime:

```haskell
PlutusTx.makeLift ''Campaign
```

Now we need to figure out what the campaign will look like on the blockchain. Which transactions are involved, who submits them, and in what order?

Each contributor pays their contribution to the address of the campaign script. When the slot `endDate` is reached, the campaign owner submits a single transaction, spending all inputs from the campaign address and paying them to a pubkey address. If the funding target isn't reached, or the campaign owner fails to collect the funds, then each contributor can claim a refund, in the form of a transaction that spends their own contribution. This means that the validator script is going to be run once per contribution, and we need to tell it which of the two cases outcomes it should check.

We can encode the two possible actions in a data type called `Action`.

```haskell
data CampaignAction = Collect | Refund
PlutusTx.makeLift ''CampaignAction
```

Now we need one final bit of information, namely the identity (public key) of each contributor, so that we know the recipient of the refund. This data can't be part of the redeemer script because then a reclaim could be made by anyone, not just the original contributor. Therefore the public key is going to be stored in the data script of the contribution.

```haskell
data Contributor = Contributor PubKey
PlutusTx.makeLift ''Contributor
```

**Note (What is the role of the data script?)** Pay-to-script outputs contain a (hash of a) validator script and a data script, but their address is the hash of the validator script only, not of the data script. The wallet uses the address to track the state of a contract, by watching the outputs at that address. So the separate data script allows us to have multiple outputs belonging to the same contract but with different data scripts.

In the crowdfunding campaign the data script contains a `Contributor` value, which is used to verify the "refund" transaction. If that data was part of the validator script, then each contribution would go to a unique address, and the campaign owner would have to be informed of all the addresses through some other mechanism.

## 1.2 The Validator Script

The general form of a validator script is `DataScript -> RedeemerScript -> PendingTx -> Bool`. The types of data and redeemer scripts are `Contributor` and `CampaignAction`, respectively, so the signature of the validator script is:

```haskell
type CampaignValidator = Contributor -> CampaignAction -> PendingTx -> Bool
```

If we want to implement `CampaignValidator` we need to have access to the parameters of the campaign, so that we can check if the selected `CampaignAction` is allowed. In Haskell we can do this by writing a function `mkValidator :: Campaign -> CampaignValidator` that takes a `Campaign` and produces a `CampaignValidator`. However, we need to wrap `mkValidator` in Template Haskell quotes so that it can be compiled to Plutus Core. To apply the compiled `mkValidator` function to the `campaign :: Campaign` argument that is provided at runtime, we use `Ledger.lifted` to get the on-chain representation of `campaign`, and apply `mkValidator` to it with `Ledger.applyScript`:

```haskell
mkValidatorScript :: Campaign -> ValidatorScript
mkValidatorScript campaign = ValidatorScript val where
  val = L.applyScript mkValidator (L.lifted campaign)
  mkValidator = L.fromCompiledCode $$(PlutusTx.compile [||
              \(c :: Campaign) (con :: Contributor) (act :: CampaignAction) (p :: PendingTx) ->
```

You may wonder why we use `L.applyScript` to supply the `Campaign` argument. Why can we not write `$$(L.lifted campaign)` inside the validator script? The reason is that `campaign` is not known at the time the validator script is compiled. The names of `lifted` and `compile` indicate their chronological order: `mkValidator` is compiled (via a compiler plugin) to Plutus Core when GHC compiles the contract module, and the `campaign` value is lifted to Plutus Core at runtime, when the contract module is executed. But we know that `mkValidator` is a function, and that is why we can apply it to the campaign definition.

Before we check whether `act` is permitted, we define a number of intermediate values that will make the checking code much more readable. These definitions are placed inside a `let` block, which is closed by a corresponding `in` below.

```haskell
              let
                  signedBy :: PendingTx -> PubKey -> Bool
                  signedBy = V.txSignedBy
```

There is no standard library of functions that are automatically in scope for on-chain code, so we need to import the ones that we want to use from the [`Ledger.Validation`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Ledger-Validation.html) module using the `$$()` splicing operator. [`Ledger.Validation`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Ledger-Validation.html) contains a subset of the standard Haskell prelude, exported as Template Haskell quotes. Code from other libraries can only be used in validator scripts if it is available as a Template Haskell quote (so we can use `$$()` to splice it in).

Next, we pattern match on the structure of the [`PendingTx`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Ledger-Validation.html#t:PendingTx) value `p` to get the Validation information we care about:

```haskell
                  PendingTx ins outs _ _ _ txnValidRange _  _ = p
                  -- p is bound to the pending transaction.
```

This binds `ins` to the list of all inputs of the current transaction, `outs` to the list of all its outputs, and `txnValidRange` to the validity interval of the pending transaction.

In the extended UTXO model with scripts that underlies Plutus, each transaction has a validity range, an interval of slots during which it may be validated by core nodes. The validity interval is passed to validator scripts via the `PendingTx` argument, and it is the only information we have about the current time. For example, if `txnValidRange` was the interval between slots 10 and 20, then we would know that the current slot number is greater than or equal to 10, and less than 20 (the interval is inclusive-exclusive). In terms of clock time we could say that the current time is between the beginning of slot 10 and the end of slot 19.

The three underscores in the match stand for fields whose values are not relevant for validating the crowdfunding transaction. The fields are `pendingTxFee` (the fee of this transaction), `pendingTxForge` (how much, if any, value was forged) and `PendingTxIn` (the current [transaction input](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Ledger-Validation.html#t:PendingTxIn)) respectively. You can click the link [`PendingTx`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Ledger-Validation.html#t:PendingTx) to learn more about the data that is available.

We also need the parameters of the campaign, which we can get by pattern matching on `c`.

```haskell
                  Campaign target deadline collectionDeadline campaignOwner = c
```

Then we compute the total value of all transaction inputs, using `foldr` on the list of inputs `ins`. Note that there is a limit on the number of inputs a transaction may have, and thus on the number of contributions in this crowdfunding campaign. In this tutorial we ignore that limit, because it depends on the details of the implementation of Plutus on the Cardano chain, and that implementation has not happened yet.

```haskell
                  totalInputs :: Ada
                  totalInputs =
                        -- define a function "addToTotal" that adds the ada
                        -- value of a 'PendingTxIn' to the total
                        let addToTotal (PendingTxIn _ _ vl) total =
                                let adaVl = Ada.fromValue vl
                                in Ada.plus total adaVl

                        -- Apply "addToTotal" to each transaction input,
                        -- summing up the results
                        in foldr addToTotal Ada.zero ins
```

We now have all the information we need to check whether the action `act` is allowed. This will be computed as

```haskell
                  isValid = case act of
                      Refund ->
                          let
                              Contributor pkCon = con
```

In the `Refund` branch we check that the outputs of this transaction all go to the contributor identified by `pkCon`. To that end we define a predicate

```haskell
                              contribTxOut :: PendingTxOut -> Bool
                              contribTxOut o =
                                case V.pubKeyOutput o of
                                  Nothing -> False
                                  Just pk -> V.eqPubKey pk pkCon
```

We check if `o` is a pay-to-pubkey output. If it isn't, then the predicate `contribTxOut` is false. If it is, then we check if the public key matches the one we got from the data script.

The predicate `contribTxOut` is applied to all outputs of the current transaction:

```haskell
                              contributorOnly = all contribTxOut outs
```

For the contribution to be refundable, three conditions must hold. The collection deadline must have passed, all outputs of this transaction must go to the contributor `con`, and the transaction was signed by the contributor. To check whether the collection deadline has passed, we use `S.before :: Slot -> SlotRange -> Bool`. `before` is exported by the `Ledger.Slot` module, alongside other useful functions for working with `SlotRange` values.

```haskell
                              refundable = S.before collectionDeadline txnValidRange &&
                                           contributorOnly &&
                                           p `signedBy` pkCon
```

The overall result of this branch is the `refundable` value:

```haskell
                          in refundable
```

The second branch represents a successful campaign.

```haskell
                      Collect ->
```

In the `Collect` case, the current slot must be between `deadline` and `collectionDeadline`, the target must have been met, and and transaction has to be signed by the campaign owner. We use `interval :: Slot -> Slot -> SlotRange` and `contains :: SlotRange -> SlotRange -> Bool` from the `Ledger.Slot` module to ensure that the spending transactions validity range, `txnValidRange`, is completely contained in the time between campaign deadline and collection deadline.

```haskell
                          S.contains (I.interval deadline collectionDeadline) txnValidRange &&
                          Ada.geq totalInputs target &&
                          p `signedBy` campaignOwner

              in isValid ||])
```

**Note (Builtins in On-Chain Code)** We can use the functions `greaterThanInteger`, `lessThanInteger`, `greaterThanEqInteger`, `lessThanEqInteger` and `equalsInteger` from the `Language.PlutusTx.Builtins` module to compare `Int` values in PLC without having to define them in the script itself, as we did with `&&`. The compiler plugin that translates Haskell Core to Plutus Core knows about those functions because `Int` is a primitive type in Plutus Core and operations on it are built in. `Bool` on the other hand is treated like any other user-defined data type, and all functions that operate on it must be defined locally. More details can be found in the [PlutusTx tutorial](../plutus-tx/tutorial/Tutorial.md).

## 1.3 Contract Endpoints

Now that we have the validator script, we need to set up contract endpoints for contributors and the campaign owner. The endpoints for the crowdfunding campaign are more complex than the endpoints of the guessing game because we need to do more than just create or spend a single transaction output. As a contributor we need to watch the campaign and claim a refund if it fails. As the campaign owner we need to collect the funds, but only if the target has been reached before the deadline has passed.

Both tasks can be implemented using *blockchain triggers*.

### Blockchain Triggers

The wallet API allows us to specify a pair of [`EventTrigger`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#t:EventTrigger) and [`EventHandler`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:EventHandler) to automatically run `collect`. An event trigger describes a condition of the blockchain and can be true or false. There are four basic triggers: [`slotRangeT`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:slotRangeT) is true when the slot number is in a specific range, [`fundsAtAddressGeqT`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:fundsAtAddressGeqT) is true when the total value of unspent outputs at an address is within a range, [`alwaysT`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:alwaysT) is always true and [`neverT`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:neverT) is never true. We also have boolean connectives [`andT`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:andT), [`orT`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:orT) and [`notT`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:notT) to describe more complex conditions.

We will need to know the address of a campaign, which amounts to  hashing the output of `mkValidatorScript`:

```haskell
campaignAddress :: Campaign -> Address
campaignAddress cmp = L.scriptAddress (mkValidatorScript cmp)
```

Contributors put their public key in a data script:

```haskell
mkDataScript :: PubKey -> DataScript
mkDataScript pk = DataScript (L.lifted (Contributor pk))
```

When we want to spend the contributions we need to provide a [`RedeemerScript`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Ledger-Scripts.html#v:RedeemerScript) value. In our case this is just the `CampaignAction`:

```haskell
mkRedeemer :: CampaignAction -> RedeemerScript
mkRedeemer action = RedeemerScript (L.lifted (action))
```

### The `collect` endpoint

The `collect` endpoint does not require any user input, so it can be run automatically as soon as the campaign is over, provided the campaign target has been reached. The function `collectFundsTrigger` gives us the `EventTrigger` that describes a successful campaign.

```haskell
collectFundsTrigger :: Campaign -> EventTrigger
collectFundsTrigger c = W.andT
    -- We use `W.intervalFrom` to create an open-ended interval that starts
    -- at the funding target.
    (W.fundsAtAddressGeqT (campaignAddress c) (Ada.toValue (fundingTarget c)))

    -- With `W.interval` we create an interval from the campaign's end date
    -- (inclusive) to the collection deadline (exclusive)
    (W.slotRangeT (W.interval (endDate c) (collectionDeadline c)))
```

`fundsAtAddressGeqT` and `slotRangeT` take `Value` and `Interval Slot` arguments respectively. The [`Interval`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#t:Interval) type is part of the `wallet-api` package. The [`Ledger.Interval`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Ledger-Interval.html#v:Interval) module that originally defines it illustrates how to write a data type and associated operations that can be used both in off-chain and in on-chain code.

The campaign owner can collect contributions when two conditions hold: The funds at the address must have reached the target, and the current slot must be greater than the campaign deadline but smaller than the collection deadline.

Now we can define an event handler that collects the contributions:

```haskell
collectionHandler :: MonadWallet m => Campaign -> EventHandler m
collectionHandler cmp = EventHandler (\_ -> do
```

`EventHandler` is a function of one argument, which we ignore in this case (the argument tells us which of the conditions in the trigger are true, which can be useful if we used [`orT`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:orT) to build a complex condition). In our case we don't need this information because we know that both the [`fundsAtAddressGeqT`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:fundsAtAddressGeqT) and the [`slotRangeT`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:slotRangeT) conditions hold when the event handler is run, so we can call [`collectFromScript`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:collectFromScript) immediately.

To collect the funds we use [`collectFromScript`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:collectFromScript), which expects a validator script and a redeemer script.

```haskell
        W.logMsg "Collecting funds"
        let redeemerScript = mkRedeemer Collect
            range          = W.interval (endDate cmp) (collectionDeadline cmp)
        W.collectFromScript range (mkValidatorScript cmp) redeemerScript)
```

Note that the trigger mechanism is a feature of the wallet, not of the blockchain. That means that the wallet needs to be running when the condition becomes true, so that it can react to it and submit transactions. Anything that happens in an [`EventHandler`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#t:EventHandler) is a normal interaction with the blockchain facilitated by the wallet.

With that, we can write the `scheduleCollection` endpoint to register a `collectFundsTrigger` and collect the funds automatically if the campaign is successful:

```haskell
scheduleCollection :: MonadWallet m => Campaign -> m ()
scheduleCollection cmp = W.register (collectFundsTrigger cmp) (collectionHandler cmp)
```

Now the campaign owner only has to run `scheduleCollection` at the beginning of the campaign and the wallet will collect the funds automatically.

This takes care of the functionality needed by campaign owners. We need another contract endpoint for making contributions and claiming a refund in case the goal was not reached.

### The `contribute` endpoint

After contributing to a campaign we do not need any user input to determine whether we are eligible for a refund of our contribution. Eligibility is defined entirely in terms of the blockchain state, and therefore we can use the event mechanism to automatically process our refund.

To contribute to a campaign we need to pay the desired amount to a script address, and provide our own public key as the data script. In the [guessing game](./02-validator-scripts.md) we used [`payToScript_`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:payToScript_), which returns `()` instead of the transaction that was submitted. For the crowdfunding contribution we need to hold on the transaction. Why?

Think back to the `guess` action of the game. We used [`collectFromScript`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:collectFromScript) to collect *all* outputs at the game address. This works only if all all outputs are unlocked by the same redeemer (see also exercise 3 of the previous tutorial).

In our crowdfunding campaign, the redeemer is a signed `Action`. In case of a refund, we sign the `Refund` action with our public key, allowing us to unlock our own contribution. But if we try to use the same redeemer to unlock other contributions the script will fail, invalidating the entire transaction. We therefore need a way to restrict the outputs that [`collectFromScript`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:collectFromScript) spends. To achieve this, the wallet API provides [`collectFromScriptTxn`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:collectFromScriptTxn), which takes an additional `TxId` parameter and only collects outputs produced by that transaction. To get the `TxId` parameter we need to hold on to the transaction that commits our contribution, which we can do with [`payToScript`](https://input-output-hk.github.io/plutus/wallet-api-0.1.0.0/html/Wallet-API.html#v:payToScript).

```haskell
refundHandler :: MonadWallet m => TxId -> Campaign -> EventHandler m
refundHandler txid cmp = EventHandler (\_ -> do
    W.logMsg "Claiming refund"
    let redeemer  = mkRedeemer Refund
        range     = W.intervalFrom (collectionDeadline cmp)
    W.collectFromScriptTxn range (mkValidatorScript cmp) redeemer txid)
```

Now we can register the refund handler when we make the contribution. The condition for being able to claim a refund is

```haskell
refundTrigger :: Campaign -> EventTrigger
refundTrigger c = W.andT
    (W.fundsAtAddressGtT (campaignAddress c) Value.zero)
    (W.slotRangeT (W.intervalFrom (collectionDeadline c)))
```

The `contribute` action has two effects: It makes the contribution using the wallet API's `payToScript` function, and it registers a trigger to automatically claim a refund if it is possible to do so.

```haskell
contribute :: MonadWallet m => Campaign -> Ada -> m ()
contribute cmp adaAmount = do
      pk <- W.ownPubKey
      let dataScript = mkDataScript pk
          amount = Ada.toValue adaAmount

      -- payToScript returns the transaction that was submitted
      -- (unlike payToScript_ which returns unit)
      tx <- W.payToScript W.defaultSlotRange (campaignAddress cmp) amount dataScript
      W.logMsg "Submitted contribution"

      -- L.hashTx gives the `TxId` of a transaction
      let txId = L.hashTx tx

      W.register (refundTrigger cmp) (refundHandler txId cmp)
      W.logMsg "Registered refund trigger"
```

# 2. Testing the Contract

There are two ways to test a Plutus contract. We can run it interactively in the [Playground](https://prod.playground.plutus.iohkdev.io/), or test it like any other program by writing some unit and property tests. Both methods give the same results because they do the same thing behind the scenes: Generate some transactions and evaluate them on the mockchain. The emulator performs the same validity checks (including running the compiled scripts) as the slot leader would for the real blockchain, so we can be confident that our contract works as expected when we deploy it.

## 2.1 Playground

We need to tell the Playground what our contract endpoints are, so that it can generate a UI for them. This is done by adding a call to [`mkFunctions`](https://input-output-hk.github.io/plutus/plutus-playground-lib-0.1.0.0/html/Playground-Contract.html#v:mkFunctions) for the endpoints to the end of the script:

```
$(mkFunctions ['scheduleCollection, 'contribute])
```

(We can't use the usual Haskell syntax highlighting for this line because the entire script is compiled and executed as part of the test suite for the `wallet-api` project. The Playground-specific [`mkFunctions`](https://input-output-hk.github.io/plutus/plutus-playground-lib-0.1.0.0/html/Playground-Contract.html#v:mkFunctions) is defined in a different library (`plutus-playground-lib`) and it is not available for this tutorial.)

Alternatively, you can click the "Crowdfunding" button in the Playground to load the sample contract including the `mkFunctions` line. Note that the sample code differs slightly from what is written in this tutorial, because it does not include some of the intermediate definitions of contract endpoints such as `startCampaign` (which was superseded by `scheduleCollection`) and `contribute` (superseded by `contribute2`).

Either way, once the contract is defined we click "Compile" to get a list of endpoints:

![Compiling a contract](compile-contract.gif)

We can then simulate a campaign by adding actions for `scheduleCollection` and `contribute`. Note that we also need to add a number of empty blocks to make sure the time advances past the `endDate` of the campaign.

![Contract actions](actions.PNG)

A click on "Evaluate" runs the simulation and returns the result. We can see in the logs that the campaign finished successfully:

![Logs](logs.png)

## 2.2 Emulator

Testing contracts with unit and property tests requires more effort than running them in the Playground, but it has several advantages. In a unit test we have much more fine-grained control over the mockchain. For example, we can simulate network outages that cause a wallet to fall behind in its notifications, and we can deploy multiple contracts on the same mockchain to see how they interact. And by writing smart contracts the same way as all other software we can use the same tools (versioning, continuous integration, release processes, etc.) without having to set up additional infrastructure.

We plan to write a tutorial on this soon. Until then we would like to refer you to the test suite in [Crowdfunding.hs](../../../plutus-use-cases/test/Spec/Crowdfunding.hs).

You can run the test suite with `nix build -f default.nix localPackages.plutus-use-cases` or `cabal test plutus-use-cases`.

# 3. Problems / Questions

1. Run traces for successful and failed campaigns
2. Change the validator script to produce more detailed log messages using `traceH`
3. Write a variation of the crowdfunding campaign that uses

```
data Campaign = Campaign {
      fundingTargets     :: [(Slot, Ada)],
      collectionDeadline :: Slot,
      campaignOwner      :: PubKey
 }
```

where `fundingTargets` is a list of slot numbers with associated Ada amounts. The campaign is successful if the funding target for one of the slots has been reached *before* that slot begins. For example, campaign with
`Campaign [(Slot 20, Ada 100), (Slot 30, Ada 200)]` is successful if the contributions amount to 100 Ada or more by slot 20, or 200 Ada or more by slot 30.

Solutions to these problems can be found [`Solutions0.hs`](../../tutorial/Tutorial/Solutions0.hs).
