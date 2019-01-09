# wallet-api: Wallet-API tutorial

This tutorial shows how to implement a simple crowdfunding campaign as a Plutus contract, using the wallet API submit it to the blockchain. The tutorial is written as a literate Haskell file, so it can be fed directly to the Haskell compiler. There are two ways to run the code:

1. Open the [Plutus Playground](https://prod.playground.plutus.iohkdev.io/), delete all the text in the editor field, and type / copy the code bits in there. Make sure to preserve the indentation.
2. Clone the Plutus repository at `git@github.com:input-output-hk/plutus.git` and build the `wallet-api` library using `nix-build -A localPackages.wallet-api`. This runs the `wallet-api-doctests` test suite that compiles the tutorial. Alternatively, run `cabal test wallet-api`. Note that the test suite requires Unix symlinks to be supported by the file system, which means that it will not work on Windows Subsystem for Linux (WSL), even though nix generally does work!

```haskell
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -O0 #-}
module Tutorial where
```

We need some imports:

```haskell
import qualified Language.PlutusTx            as PlutusTx
import           Ledger
import           Ledger.Validation            as Validation
import           Wallet
import           Wallet.Emulator
import           Prelude                      hiding ((&&))
import           GHC.Generics                 (Generic)
```

The module imported as `Validation` contains types and functions that can be used in on-chain code. `PlutusTx` lets us translate code between Haskell and Plutus Core (see the [PlutusTx tutorial](https://github.com/input-output-hk/plutus/blob/master/plutus-tx/tutorial/Tutorial.md)). `Wallet.Emulator` covers interactions with the wallet, for example generating the transactions that actually get the crowdfunding contract onto the blockchain.

The campaign has the following parameters:

* Funding target
* End date
* Collection deadline
* Campaign owner

If the funding target is reached at the end date, then the campaign owner may collect all the funds. If it isn't reached, or if the owner does not collect the funds before the collection deadline, then the contributors are entitled to a refund.

In Haskell:

```haskell
data Campaign = Campaign {
      fundingTarget      :: Value,
      endDate            :: Slot,
      collectionDeadline :: Slot,
      campaignOwner      :: PubKey
 }
```

The type of monetary values is `Value`. Dates are expressed in terms of slots, and their type is `Slot`. The campaign owner is identified by their public key.

One of the strengths of PlutusTx is the ability to use the same definitions for on-chain and off-chain code, which includes lifting values from Haskell to Plutus Core. To enable values of the `Campaign` type to be lifted, we need to call `makeLift` from the `PlutusTx` module:

```haskell
PlutusTx.makeLift ''Campaign
```

Now we need to figure out what the campaign will look like on the blockchain. Which transactions are involved, who submits them, and in what order?

Each contributor pays their contribution to the address of the campaign script. When the slot `endDate` is reached, the campaign owner submits a single transaction, spending all inputs from the campaign address and paying them to a pubkey address. If the funding target isn't reached, or the campaign owner fails to collect the funds, then each contributor can claim a refund, in the form of a transaction that spends their own contribution. This means that the validator script is going to be run once per contribution, and we need to tell it which of the two cases outcomes it should check.

We can encode the two possible actions in a data type:

```haskell
data CampaignAction = Collect Signature | Refund Signature
PlutusTx.makeLift ''CampaignAction
```

The `CampaignAction` will be submitted as the redeemer script. Now we need one final bit of information, namely the identity (public key) of each contributor, so that we know the recipient of the refund. This data can't be part of the redeemer script because then a reclaim could be made by anyone, not just the original contributor. Therefore the public key is going to be stored in the data script of the contribution.

```haskell
data Contributor = Contributor PubKey
PlutusTx.makeLift ''Contributor
```

Now that we know the types of data and redeemer scripts, we automatically know the signature of the validator script:

```haskell
type CampaignValidator = CampaignAction -> Contributor -> PendingTx -> ()
```

`CampaignValidator` is a function that takes three parameters -- `CampaignAction`, `Contributor`, and `PendingTx` and produces a unit value `()` or fails with an error.

If we want to implement `CampaignValidator` we need to know the parameters of the campaign, so that we can check if the selected `CampaignAction` is allowed. In Haskell we can do this by writing a function `mkValidator :: Campaign -> CampaignValidator` that takes a `Campaign` and produces a `CampaignValidator`. However, we can't implement `mkValidator` like this, because we need to wrap it in Template Haskell quotes so that it can be compiled to Plutus Core. We therefore define `mkValidator` in PlutusTx:

```haskell
mkValidatorScript :: Campaign -> ValidatorScript
mkValidatorScript campaign = ValidatorScript val where
  val = applyScript mkValidator (lifted campaign)
  -- ^ val is the obtained by applying `mkValidator` to the lifted `campaign` value
  mkValidator = fromCompiledCode $$(PlutusTx.compile [||
```

Anything between the `[||` and `||]` quotes is going to be _on-chain code_ and anything outside the quotes is _off-chain code_. We can now implement a lambda function that looks like `mkValidator`, starting with its parameters:

```haskell
              \(c :: Campaign) (act :: CampaignAction) (con :: Contributor) (p :: PendingTx) ->
```

Before we check whether `act` is permitted, we define a number of intermediate values that will make the checking code much more readable. These definitions are placed inside a `let` block, which is closed by a corresponding `in` below.

```haskell
              let
                  infixr 3 &&
                  (&&) :: Bool -> Bool -> Bool
                  (&&) = $$(PlutusTx.and)

                  signedBy :: PubKey -> Signature -> Bool
                  signedBy (PubKey pk) (Signature s) = pk == s
```

There is no standard library of functions that are automatically in scope for on-chain code, so we need to import the ones that we want to use from the `Validation` module using the `\$\$()` splicing operator.

Next, we pattern match on the structure of the `PendingTx` value `p` to get the Validation information we care about:

```haskell
                  PendingTx ins outs _ _ (Slot currentSlot) _ = p
```

This binds `ins` to the list of all inputs of the current transaction, `outs` to the list of all its outputs, and `currentSlot` to the current slot (that is, to the current date).

We also need the parameters of the campaign, which we can get by pattern matching on `c`.

```haskell
                  Campaign (Value target) (Slot deadline) (Slot collectionDeadline) campaignOwner = c
```

Then we compute the total value of all transaction inputs, using `Validation.foldr` on the list of inputs `ins`.

```haskell
                  totalInputs :: Int
                  totalInputs =
                      let v (PendingTxIn _ _ (Value vl)) = vl in
                      $$(PlutusTx.foldr) (\i total -> total + v i) 0 ins
```

We now have all the information we need to check whether the action `act` is allowed. This will be computed as

```haskell
                  isValid = case act of
                      Refund sig ->
                          let
                              Contributor pkCon = con
```

In the `Refund` branch we check that the outputs of this transaction all go to the contributor identified by `pkCon`. To that end we define a predicate

```haskell
                              contributorTxOut :: PendingTxOut -> Bool
                              contributorTxOut o =
                                case $$(Validation.pubKeyOutput) o of
                                  Nothing -> False
                                  Just pk -> $$(Validation.eqPubKey) pk pkCon
```

We check if `o` is a pay-to-pubkey output. If it isn't, then the predicate `contributorTxOut` is false. If it is, then we check if the public key matches the one we got from the data script.

The predicate `contributorTxOut` is applied to all outputs of the current transaction:

```haskell
                              contributorOnly = $$(PlutusTx.all) contributorTxOut outs
```

For the contribution to be refundable, three conditions must hold. The collection deadline must have passed, all outputs of this transaction must go to the contributor `con`, and the transaction was signed by the contributor.

```haskell
                              refundable   = currentSlot > collectionDeadline &&
                                      contributorOnly &&
                                      pkCon `signedBy` sig
```

The overall result of this branch is the `refundable` value:

```haskell
                          in refundable
```

The second branch represents a successful campaign.

```haskell
                      Collect sig ->
```

In the `Collect` case, the current slot must be between `deadline` and `collectionDeadline`, the target must have been met, and and transaction has to be signed by the campaign owner.

```haskell
                          currentSlot > deadline &&
                          currentSlot <= collectionDeadline &&
                          totalInputs >= target &&
                          campaignOwner `signedBy` sig

              in
```

Finally, we can return the unit value `()` if `isValid` is true, or fail with an error otherwise.

```haskell
              if isValid then () else ($$(PlutusTx.error) ())
                  ||])
```

We need to compute the address of a campaign, which amounts to  hashing the output of `mkValidatorScript`:

```haskell
campaignAddress :: Campaign -> Address'
campaignAddress cmp = scriptAddress (mkValidatorScript cmp)
```

Now that we have the validator script, we need to set up wallet actions for contributors and the campaign owner. Contributors put their public key in a data script:

```haskell
mkDataScript :: PubKey -> DataScript
mkDataScript pk = DataScript (lifted (Contributor pk))
```

Wallet actions have the return type `MockWallet ()`, which means that they can use the wallet API to create and submit transactions, query blockchain addresses, and log messages. `MockWallet` indicates that this wallet action can be run by the emulator, so you don't need to have a testnet available. When the contract is ready to be deployed, we simply change the type to `CardanoWallet`.

```haskell
contribute :: Campaign -> Value -> MockWallet ()
contribute cmp amount = do
```

Contributing to a campaign is easy: We need to pay the value `amount` to a script address, and provide our own public key as the data script.

```haskell
      pk <- ownPubKey
      let dataScript = mkDataScript pk
      tx <- payToScript (campaignAddress cmp) amount dataScript
```

`tx` is a transaction that pays `amount` to the address of the campaign validator script, using our own public key as the data script.

```haskell
      -- TODO: In the original contract we now register a refund trigger for our own contribution, using the hash of `tx`.
      pure ()
```

When we want to spend the contributions we need to provide a `RedeemerScript` value. In our case this is just the `CampaignAction`:

```haskell
mkRedeemer :: CampaignAction -> RedeemerScript
mkRedeemer action = RedeemerScript (lifted (action))
```

To collect the funds we use `collectFromScript`, which expects a validator script and a redeemer script.

```haskell
collect :: Signature -> Campaign -> MockWallet ()
collect sig cmp =
      let validatorScript = mkValidatorScript cmp
          redeemer = mkRedeemer $ Collect sig
      in
          collectFromScript validatorScript redeemer
```

If we run `collect` now, nothing will happen. Why? Because in order to spend all outputs at the script address, the wallet needs to be aware of this address _before_ the outputs are produced. That way, it can scan incoming blocks from the blockchain for contributions to that address, and doesn't have to keep a record of all unspent outputs of the entire blockchain. So before the campaign starts, the campaign owner needs to run the following action:

```haskell
startCampaign :: Campaign -> MockWallet ()
startCampaign campaign = startWatching (campaignAddress campaign)
```

`startCampaign`, `contribute` and `collect` form the public interface of the crowdfunding campaign.

# Blockchain triggers

Some interactions with contracts can be automated. For example, the `collect` endpoint does not require any user input, so it could be run automatically as soon as the campaign is over, provided the campaign target has been reached. 

The wallet API allows us to specify `EventTrigger`s with handlers to implement this. An event trigger describes a condition of the blockchain and can be true or false. There are four basic triggers: `slotRangeT` is true when the slot number is in a specific range, `fundsAtAddressT` is true when the total value of unspent outputs at an address is within a range, `alwaysT` is always true and `neverT` is never true. We also have boolean connectives `andT`, `orT` and `notT` to describe more complex conditions.

```haskell
collectFundsTrigger :: Campaign -> EventTrigger
collectFundsTrigger c = andT
    (fundsAtAddressT (campaignAddress c) (GEQ (fundingTarget c)))
    (slotRangeT (Interval (endDate c) (collectionDeadline c)))
```

The campaign owner can collect contributions when two conditions hold: The funds at the address must have reached the target, and the current slot must be greater than the campaign deadline but smaller than the collection deadline.

Now we can define an event handler that collects the contributions:

```haskell
collection :: Campaign -> EventHandler MockWallet
collection cmp = EventHandler (\_ -> do
        logMsg "Collecting funds"
        let redeemerScript = Ledger.RedeemerScript (Ledger.lifted Collect)
        collectFromScript (mkValidatorScript cmp) redeemerScript)
```

The handler is function of one argument, which we ignore in this case (the argument tells us which of the conditions in the trigger are true, which can be useful if we used `orT` to build a complex condition). In our case we don't need this information because we know that both the `fundsAtAddressT` and the `slotRangeT` conditions hold when the event handler is run, so we can call `collectFromScript` immediately.

Note that the trigger mechanism is a feature of the wallet, not of the blockchain. That means that the wallet needs to be running when the condition becomes true, so that it can submit transactions. It also means that there is no guarantee that the transaction(s) we generate in the handler are valid. Anything that happens in an `EventHandler` is a normal interaction with the blockchain facilitated by the wallet, so it is still our responsibility to submit valid transactions. 

With that, we can re-write the `startCampaign` endpoint to register a `collectFundsTrigger` and collect the funds automatically if the campaign is successful:

```haskell
scheduleCollection :: Campaign -> MockWallet ()
scheduleCollection cmp = register (collectFundsTrigger cmp) (collection cmp)
```

Now the campaign owner only has to run `scheduleCollection` at the beginning of the campaign and the wallet will take care of collecting the funds.

# Testing the contract in the playground


# Testing the contract in the emulator

(TBD)

