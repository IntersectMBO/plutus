-- | Crowdfunding contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction. This is, of course, limited by the maximum
-- number of inputs a transaction can have.
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
module Language.PlutusTx.Coordination.Contracts.CrowdFunding (
    -- * Campaign parameters
    Campaign(..)
    -- * Functionality for campaign contributors
    , contribute
    -- * Functionality for campaign owners
    , scheduleCollection
    , campaignAddress
    -- * Validator script
    , contributionScript
    , mkCampaign
    ) where

import qualified Language.PlutusTx           as PlutusTx
import           Ledger.Slot                 (SlotRange)
import qualified Ledger.Slot                 as Slot
import qualified Language.PlutusTx.Prelude   as P
import           Ledger
import           Ledger.Validation           as V
import           Ledger.Value                (Value)
import qualified Ledger.Value                as VTH
import           Wallet                      as W
import qualified Wallet.Emulator             as EM
import           Wallet.Emulator             (Wallet)

import           Prelude                     hiding ((&&))

-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: Slot
    -- ^ The date by which the campaign target has to be met
    , campaignTarget             :: Value
    -- ^ Target amount of funds
    , campaignCollectionDeadline :: Slot
    -- ^ The date by which the campaign owner has to collect the funds
    , campaignOwner              :: PubKey
    -- ^ Public key of the campaign owner. This key is entitled to retrieve the
    --   funds if the campaign is successful.
    }

PlutusTx.makeLift ''Campaign

-- | Construct a 'Campaign' value from the campaign parameters,
--   using the wallet's public key.
mkCampaign :: Slot -> Value -> Slot -> Wallet -> Campaign
mkCampaign ddl target collectionDdl ownerWallet =
    Campaign
        { campaignDeadline = ddl
        , campaignTarget   = target
        , campaignCollectionDeadline = collectionDdl
        , campaignOwner = EM.walletPubKey ownerWallet
        }

-- | The 'SlotRange' during which the funds can be collected
collectionRange :: Campaign -> SlotRange
collectionRange cmp =
    W.interval (campaignDeadline cmp) (campaignCollectionDeadline cmp)

-- | The 'SlotRange' during which a refund may be claimed
refundRange :: Campaign -> SlotRange
refundRange cmp =
    W.intervalFrom (campaignCollectionDeadline cmp)

-- | Action that can be taken by the participants in this contract. A value of
--   `CampaignAction` is provided as the redeemer. The validator script then
--   checks if the conditions for performing this action are met.
--
data CampaignAction = Collect | Refund

PlutusTx.makeLift ''CampaignAction

type CrowdfundingValidator = PubKey -> CampaignAction -> PendingTx -> ()

validRefund :: Campaign -> PubKey -> PendingTx -> Bool
validRefund campaign contributor ptx =
    Slot.contains (refundRange campaign) (pendingTxValidRange ptx)
    `P.and` (ptx `V.txSignedBy` contributor)

validCollection :: Campaign -> PendingTx -> Bool
validCollection campaign p =
    (collectionRange campaign `Slot.contains` pendingTxValidRange p)
    `P.and` (valueSpent p `VTH.geq` campaignTarget campaign)
    `P.and` (p `V.txSignedBy` campaignOwner campaign)

mkValidator :: Campaign -> CrowdfundingValidator
mkValidator c con act p =
    let
        isValid = case act of
            Refund -> validRefund c con p
            Collect -> validCollection c p
    in if isValid then () else P.error ()

-- | The validator script that determines whether the campaign owner can
--   retrieve the funds or the contributors can claim a refund.
--
contributionScript :: Campaign -> ValidatorScript
contributionScript cmp  = ValidatorScript $
    $$(Ledger.compileScript [|| mkValidator ||])
        `Ledger.applyScript`
            Ledger.lifted cmp

-- | The address of a [[Campaign]]
campaignAddress :: Campaign -> Ledger.Address
campaignAddress = Ledger.scriptAddress . contributionScript

-- | Contribute funds to the campaign (contributor)
--
contribute :: MonadWallet m => Slot -> Value -> Slot -> Wallet -> Value -> m ()
contribute deadline target collectionDeadline ownerWallet contribution = do
    let cmp = mkCampaign deadline target collectionDeadline ownerWallet
    ownPK <- ownPubKey
    let ds = DataScript (Ledger.lifted ownPK)
        range = W.interval 1 (campaignDeadline cmp)
    tx <- payToScript range (campaignAddress cmp) contribution ds
    logMsg "Submitted contribution"

    register (refundTrigger contribution cmp) (refundHandler (Ledger.hashTx tx) cmp)
    logMsg "Registered refund trigger"

-- | Register a [[EventHandler]] to collect all the funds of a campaign
--
scheduleCollection :: MonadWallet m => Slot -> Value -> Slot -> Wallet -> m ()
scheduleCollection deadline target collectionDeadline ownerWallet = do
    let cmp = mkCampaign deadline target collectionDeadline ownerWallet
    register (collectFundsTrigger cmp) (EventHandler (\_ -> do
        logMsg "Collecting funds"
        let redeemerScript = Ledger.RedeemerScript (Ledger.lifted Collect)
            range = collectionRange cmp
        collectFromScript range (contributionScript cmp) redeemerScript))

-- | An event trigger that fires when a refund of campaign contributions can be claimed
refundTrigger :: Value -> Campaign -> EventTrigger
refundTrigger vl c = andT
    (fundsAtAddressT (campaignAddress c) (W.intervalFrom vl))
    (slotRangeT (refundRange c))

-- | An event trigger that fires when the funds for a campaign can be collected
collectFundsTrigger :: Campaign -> EventTrigger
collectFundsTrigger c = andT
    (fundsAtAddressT (campaignAddress c) (W.intervalFrom (campaignTarget c)))
    (slotRangeT (collectionRange c))

-- | Claim a refund of our campaign contribution
refundHandler :: MonadWallet m => TxId -> Campaign -> EventHandler m
refundHandler txid cmp = EventHandler (\_ -> do
    logMsg "Claiming refund"
    let validatorScript = contributionScript cmp
        redeemerScript  = Ledger.RedeemerScript (Ledger.lifted Refund)

    collectFromScriptTxn (refundRange cmp) validatorScript redeemerScript txid)
