{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Crowdfunding where
-- TRIM TO HERE
-- Crowdfunding contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction.
--
-- Note [Transactions in the crowdfunding campaign] explains the structure of
-- this contract on the blockchain.

import           Control.Applicative         (Applicative (pure))
import           Control.Monad               (void)
import           Ledger                      (PubKeyHash, ScriptContext (..), TxInfo (..), Validator, pubKeyHash, txId,
                                              valueSpent)
import qualified Ledger                      as Ledger
import qualified Ledger.Ada                  as Ada
import qualified Ledger.Contexts             as V
import qualified Ledger.Interval             as Interval
import qualified Ledger.Scripts              as Scripts
import           Ledger.Slot                 (Slot, SlotRange)
import qualified Ledger.Typed.Scripts        as Scripts
import           Ledger.Value                (Value)
import qualified Ledger.Value                as Value
import           Playground.Contract
import           Plutus.Contract
import qualified Plutus.Contract.Constraints as Constraints
import qualified Plutus.Contract.Typed.Tx    as Typed
import qualified PlutusTx                    as PlutusTx
import           PlutusTx.Prelude            hiding (Applicative (..), Semigroup (..))
import           Prelude                     (Semigroup (..))
import qualified Prelude                     as Haskell
import qualified Wallet.Emulator             as Emulator

-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: Slot
    -- ^ The date by which the campaign target has to be met
    , campaignTarget             :: Value
    -- ^ Target amount of funds
    , campaignCollectionDeadline :: Slot
    -- ^ The date by which the campaign owner has to collect the funds
    , campaignOwner              :: PubKeyHash
    -- ^ Public key of the campaign owner. This key is entitled to retrieve the
    --   funds if the campaign is successful.
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''Campaign

-- | Action that can be taken by the participants in this contract. A value of
--   `CampaignAction` is provided as the redeemer. The validator script then
--   checks if the conditions for performing this action are met.
--
data CampaignAction = Collect | Refund

PlutusTx.unstableMakeIsData ''CampaignAction
PlutusTx.makeLift ''CampaignAction

type CrowdfundingSchema =
    BlockchainActions
        .\/ Endpoint "schedule collection" ()
        .\/ Endpoint "contribute" Contribution

newtype Contribution = Contribution
        { contribValue :: Value
        -- ^ how much to contribute
        } deriving stock (Haskell.Eq, Show, Generic)
          deriving anyclass (ToJSON, FromJSON, ToSchema, ToArgument)

-- | Construct a 'Campaign' value from the campaign parameters,
--   using the wallet's public key.
mkCampaign :: Slot -> Value -> Slot -> Wallet -> Campaign
mkCampaign ddl target collectionDdl ownerWallet =
    Campaign
        { campaignDeadline = ddl
        , campaignTarget   = target
        , campaignCollectionDeadline = collectionDdl
        , campaignOwner = pubKeyHash $ Emulator.walletPubKey ownerWallet
        }

-- | The 'SlotRange' during which the funds can be collected
collectionRange :: Campaign -> SlotRange
collectionRange cmp =
    Interval.interval (campaignDeadline cmp) (campaignCollectionDeadline cmp)

-- | The 'SlotRange' during which a refund may be claimed
refundRange :: Campaign -> SlotRange
refundRange cmp =
    Interval.from (campaignCollectionDeadline cmp)

data Crowdfunding
instance Scripts.ScriptType Crowdfunding where
    type instance RedeemerType Crowdfunding = CampaignAction
    type instance DatumType Crowdfunding = PubKeyHash

scriptInstance :: Campaign -> Scripts.ScriptInstance Crowdfunding
scriptInstance = Scripts.validatorParam @Crowdfunding
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

{-# INLINABLE validRefund #-}
validRefund :: Campaign -> PubKeyHash -> TxInfo -> Bool
validRefund campaign contributor txinfo =
    -- Check that the transaction falls in the refund range of the campaign
    Interval.contains (refundRange campaign) (txInfoValidRange txinfo)
    -- Check that the transaction is signed by the contributor
    && (txinfo `V.txSignedBy` contributor)

validCollection :: Campaign -> TxInfo -> Bool
validCollection campaign txinfo =
    -- Check that the transaction falls in the collection range of the campaign
    (collectionRange campaign `Interval.contains` txInfoValidRange txinfo)
    -- Check that the transaction is trying to spend more money than the campaign
    -- target (and hence the target was reached)
    && (valueSpent txinfo `Value.geq` campaignTarget campaign)
    -- Check that the transaction is signed by the campaign owner
    && (txinfo `V.txSignedBy` campaignOwner campaign)

-- | The validator script is of type 'CrowdfundingValidator', and is
-- additionally parameterized by a 'Campaign' definition. This argument is
-- provided by the Plutus client, using 'PlutusTx.applyCode'.
-- As a result, the 'Campaign' definition is part of the script address,
-- and different campaigns have different addresses.
mkValidator :: Campaign -> PubKeyHash -> CampaignAction -> ScriptContext -> Bool
mkValidator c con act p = case act of
    -- the "refund" branch
    Refund  -> validRefund c con (scriptContextTxInfo p)
    -- the "collection" branch
    Collect -> validCollection c (scriptContextTxInfo p)

-- | The validator script that determines whether the campaign owner can
--   retrieve the funds or the contributors can claim a refund.
--
contributionScript :: Campaign -> Validator
contributionScript = Scripts.validatorScript . scriptInstance

-- | The address of a [[Campaign]]
campaignAddress :: Campaign -> Ledger.ValidatorHash
campaignAddress = Scripts.validatorHash . contributionScript

-- | The crowdfunding contract for the 'Campaign'.
crowdfunding :: AsContractError e => Campaign -> Contract () CrowdfundingSchema e ()
crowdfunding c = contribute c `select` scheduleCollection c

-- | A sample campaign with a target of 200 Ada by slot 20
theCampaign :: Campaign
theCampaign = Campaign
    { campaignDeadline = 40
    , campaignTarget   = Ada.lovelaceValueOf 200
    , campaignCollectionDeadline = 60
    , campaignOwner = pubKeyHash $ Emulator.walletPubKey (Emulator.Wallet 1)
    }

-- | The "contribute" branch of the contract for a specific 'Campaign'. Exposes
--   an endpoint that allows the user to enter their public key and the
--   contribution. Then waits until the campaign is over, and collects the
--   refund if the funding target was not met.
contribute :: AsContractError e => Campaign -> Contract () CrowdfundingSchema e ()
contribute cmp = do
    Contribution{contribValue} <- endpoint @"contribute"
    contributor <- pubKeyHash <$> ownPubKey
    let inst = scriptInstance cmp
        tx = Constraints.mustPayToTheScript contributor contribValue
                <> Constraints.mustValidateIn (Ledger.interval 1 (campaignDeadline cmp))
    txid <- fmap txId (submitTxConstraints inst tx)

    utxo <- watchAddressUntil (Scripts.scriptAddress inst) (campaignCollectionDeadline cmp)

    -- 'utxo' is the set of unspent outputs at the campaign address at the
    -- collection deadline. If 'utxo' still contains our own contribution
    -- then we can claim a refund.

    let flt Ledger.TxOutRef{txOutRefId} _ = txid Haskell.== txOutRefId
        tx' = Typed.collectFromScriptFilter flt utxo Refund
                <> Constraints.mustValidateIn (refundRange cmp)
                <> Constraints.mustBeSignedBy contributor
    if Constraints.modifiesUtxoSet tx'
    then void (submitTxConstraintsSpending inst utxo tx')
    else pure ()

-- | The campaign owner's branch of the contract for a given 'Campaign'. It
--   watches the campaign address for contributions and collects them if
--   the funding goal was reached in time.
scheduleCollection :: AsContractError e => Campaign -> Contract () CrowdfundingSchema e ()
scheduleCollection cmp = do
    let inst = scriptInstance cmp

    -- Expose an endpoint that lets the user fire the starting gun on the
    -- campaign. (This endpoint isn't technically necessary, we could just
    -- run the 'trg' action right away)
    () <- endpoint @"schedule collection"

    _ <- awaitSlot (campaignDeadline cmp)
    unspentOutputs <- utxoAt (Scripts.scriptAddress inst)

    let tx = Typed.collectFromScript unspentOutputs Collect
            <> Constraints.mustValidateIn (collectionRange cmp)
    void $ submitTxConstraintsSpending inst unspentOutputs tx

{- note [Transactions in the crowdfunding campaign]

Assume there is a campaign `c :: Campaign` with two contributors
(identified by public key `pc_1` and `pc_2`) and one campaign owner (pco).
Each contributor creates a transaction, `t_1` and `t_2`, whose outputs are
locked by the scripts `contributionScript c pc_1` and `contributionScript
c pc_1` respectively.

There are two outcomes for the campaign.

1. Campaign owner collects the funds from both contributors. In this case
   the owner creates a single transaction with two inputs, referring to
   `t_1` and `t_2`. Each input contains the script `contributionScript c`
   specialised to a contributor. The redeemer script of this transaction
   contains the value `Collect`, prompting the validator script to check the
   branch for `Collect`.

2. Refund. In this case each contributor creates a transaction with a
   single input claiming back their part of the funds. This case is
   covered by the `Refund` branch, and its redeemer script is the
   `Refund` action.

In both cases, the validator script is run twice. In the first case
there is a single transaction consuming both inputs. In the second case there
are two different transactions that may happen at different times.

-}

{- note [PendingTx]

This part of the API (the PendingTx argument) is experimental and subject
to change.

-}

endpoints :: AsContractError e => Contract () CrowdfundingSchema e ()
endpoints = crowdfunding theCampaign

mkSchemaDefinitions ''CrowdfundingSchema

$(mkKnownCurrencies [])
