-- | Crowdfunding contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction. This is, of course, limited by the maximum
-- number of inputs a transaction can have.
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}
module Language.PlutusTx.Coordination.Contracts.CrowdFunding (
    -- * Campaign parameters
    Campaign(..)
    , CrowdfundingSchema
    , crowdfunding
    , theCampaign
    -- * Functionality for campaign contributors
    , contribute
    -- * Functionality for campaign owners
    , scheduleCollection
    , campaignAddress
    -- * Validator script
    , contributionScript
    , mkValidator
    , mkCampaign
    , CampaignAction(..)
    , collectionRange
    , refundRange
    -- * Traces
    , startCampaign
    , makeContribution
    , successfulCampaign
    ) where

import           Control.Applicative            (Alternative(..), Applicative(..))
import           Control.Lens                   ((&), (.~), (^.))
import           Control.Monad                  (Monad((>>)), void)
import qualified Data.Set                       as Set
import           Language.Plutus.Contract
import qualified Language.Plutus.Contract.Typed.Tx as Typed
import           Language.Plutus.Contract.Trace (ContractTrace, MonadEmulator)
import qualified Language.Plutus.Contract.Trace as Trace
import qualified Language.PlutusTx              as PlutusTx
import           Language.PlutusTx.Prelude      hiding ((>>), return, (>>=), (<$>), Applicative (..))
import           Ledger                         (Address, PendingTx, PubKey, Slot, ValidatorScript)
import qualified Ledger                         as Ledger
import qualified Ledger.Ada                     as Ada
import qualified Ledger.Interval                as Interval
import           Ledger.Slot                    (SlotRange)
import qualified Ledger.Typed.Scripts           as Scripts
import           Ledger.Validation              as V
import           Ledger.Value                   (Value)
import qualified Ledger.Value                   as VTH
import           Wallet.Emulator                (Wallet)
import qualified Wallet.Emulator                as Emulator
import qualified Prelude                        as Haskell

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

-- | Action that can be taken by the participants in this contract. A value of
--   `CampaignAction` is provided as the redeemer. The validator script then
--   checks if the conditions for performing this action are met.
--
data CampaignAction = Collect | Refund

PlutusTx.makeIsData ''CampaignAction
PlutusTx.makeLift ''CampaignAction

type CrowdfundingSchema =
    BlockchainActions
        .\/ Endpoint "schedule collection" ()
        .\/ Endpoint "contribute" (PubKey, Value)

-- | Construct a 'Campaign' value from the campaign parameters,
--   using the wallet's public key.
mkCampaign :: Slot -> Value -> Slot -> Wallet -> Campaign
mkCampaign ddl target collectionDdl ownerWallet =
    Campaign
        { campaignDeadline = ddl
        , campaignTarget   = target
        , campaignCollectionDeadline = collectionDdl
        , campaignOwner = Emulator.walletPubKey ownerWallet
        }

-- | The 'SlotRange' during which the funds can be collected
collectionRange :: Campaign -> SlotRange
collectionRange cmp =
    Interval.interval (campaignDeadline cmp) (campaignCollectionDeadline cmp)

-- | The 'SlotRange' during which a refund may be claimed
refundRange :: Campaign -> SlotRange
refundRange cmp =
    Interval.from (campaignCollectionDeadline cmp)

data CrowdFunding
instance Scripts.ScriptType CrowdFunding where
    type instance RedeemerType CrowdFunding = CampaignAction
    type instance DataType CrowdFunding = PubKey

scriptInstance :: Campaign -> Scripts.ScriptInstance CrowdFunding
scriptInstance cmp = Scripts.Validator @CrowdFunding
    ($$(PlutusTx.compile [|| mkValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode cmp)
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @PubKey @CampaignAction

{-# INLINABLE validRefund #-}
validRefund :: Campaign -> PubKey -> PendingTx -> Bool
validRefund campaign contributor ptx =
    Interval.contains (refundRange campaign) (pendingTxValidRange ptx)
    && (ptx `V.txSignedBy` contributor)

{-# INLINABLE validCollection #-}
validCollection :: Campaign -> PendingTx -> Bool
validCollection campaign p =
    (collectionRange campaign `Interval.contains` pendingTxValidRange p)
    && (valueSpent p `VTH.geq` campaignTarget campaign)
    && (p `V.txSignedBy` campaignOwner campaign)

{-# INLINABLE mkValidator #-}
mkValidator :: Campaign -> PubKey -> CampaignAction -> PendingTx -> Bool
mkValidator c con act p = case act of
    Refund  -> validRefund c con p
    Collect -> validCollection c p

-- | The validator script that determines whether the campaign owner can
--   retrieve the funds or the contributors can claim a refund.
--
contributionScript :: Campaign -> ValidatorScript
contributionScript = Scripts.validatorScript . scriptInstance

-- | The address of a [[Campaign]]
campaignAddress :: Campaign -> Ledger.Address
campaignAddress = Scripts.scriptAddress . scriptInstance

-- | The crowdfunding contract for the 'Campaign'.
crowdfunding :: AsContractError e => Campaign -> Contract CrowdfundingSchema e ()
crowdfunding c = contribute c <|> scheduleCollection c

-- | A sample campaign with a target of 20 Ada by slot 20
theCampaign :: Campaign
theCampaign = Campaign
    { campaignDeadline = 20
    , campaignTarget   = Ada.lovelaceValueOf 20
    , campaignCollectionDeadline = 30
    , campaignOwner = Emulator.walletPubKey (Emulator.Wallet 1)
    }

-- | The "contribute" branch of the contract for a specific 'Campaign'. Exposes
--   an endpoint that allows the user to enter their public key and the
--   contribution. Then waits until the campaign is over, and collects the
--   refund if the funding target was not met.
contribute :: AsContractError e => Campaign -> Contract CrowdfundingSchema e ()
contribute cmp = do
    (ownPK, contribution) <- endpoint @"contribute"
    let ds = Ledger.DataScript (PlutusTx.toData ownPK)
        tx = payToScript contribution (campaignAddress cmp) ds
                & validityRange .~ Ledger.interval 1 (campaignDeadline cmp)
    txId <- writeTxSuccess tx

    utxo <- watchAddressUntil (campaignAddress cmp) (campaignCollectionDeadline cmp)
    -- 'utxo' is the set of unspent outputs at the campaign address at the
    -- collection deadline. If 'utxo' still contains our own contribution
    -- then we can claim a refund.

    let flt Ledger.TxOutRefOf{txOutRefId} _ = txId Haskell.== txOutRefId
        tx' = Typed.collectFromScriptFilter flt utxo (scriptInstance cmp) Refund
                & validityRange .~ refundRange cmp
    if not . Set.null $ tx' ^. inputs
    then void (writeTx tx')
    else pure ()

-- | The campaign owner's branch of the contract for a given 'Campaign'. It
--   watches the campaign address for contributions and collects them if
--   the funding goal was reached in time.
scheduleCollection :: Campaign -> Contract CrowdfundingSchema e ()
scheduleCollection cmp = do

    -- Expose an endpoint that lets the user fire the starting gun on the
    -- campaign. (This endpoint isn't technically necessary, we could just
    -- run the 'trg' action right away)
    () <- endpoint @"schedule collection"

    -- 'trg' describes the conditions for a successful campaign. It returns a
    -- tuple with the unspent outputs at the campaign address, and the current
    -- slot.
    _ <- awaitSlot (campaignDeadline cmp)
    unspentOutputs <- utxoAt (campaignAddress cmp)

    let tx = Typed.collectFromScriptFilter (\_ _ -> True) unspentOutputs (scriptInstance cmp) Collect
            & validityRange .~ collectionRange cmp
    void $ writeTx tx

-- | Call the "schedule collection" endpoint and instruct the campaign owner's
--   wallet (wallet 1) to start watching the campaign address.
startCampaign
    :: ( MonadEmulator e m  )
    => ContractTrace CrowdfundingSchema e m () ()
startCampaign =
    Trace.callEndpoint @"schedule collection" (Trace.Wallet 1)  ()
        >> Trace.notifyInterestingAddresses (Trace.Wallet 1)

-- | Call the "contribute" endpoint, contributing the amount from the wallet
makeContribution
    :: ( MonadEmulator e m )
    => Wallet
    -> Value
    -> ContractTrace CrowdfundingSchema e m () ()
makeContribution w v =
    Trace.callEndpoint @"contribute" w (Trace.walletPubKey w, v)
        >> Trace.handleBlockchainEvents w

-- | Run a successful campaign with contributions from wallets 2, 3 and 4.
successfulCampaign
    :: ( MonadEmulator e m )
    => ContractTrace CrowdfundingSchema e m () ()
successfulCampaign =
    startCampaign
        >> makeContribution (Trace.Wallet 2) (Ada.lovelaceValueOf 10)
        >> makeContribution (Trace.Wallet 3) (Ada.lovelaceValueOf 10)
        >> makeContribution (Trace.Wallet 4) (Ada.lovelaceValueOf 1)
        >> Trace.addBlocks 18
        >> Trace.notifySlot (Trace.Wallet 1)
        >> Trace.handleBlockchainEvents (Trace.Wallet 1)
